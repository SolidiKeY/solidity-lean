#!/usr/bin/env python3
import argparse,os,subprocess,json,sys,statistics
from pathlib import Path
parser=argparse.ArgumentParser(description="Matched serial Lean elaboration/kernel checks. Run under the shared writer lock after fetching the Lake cache; no systemd scope on cloud VM (H232). Requires the pinned prototype worktree and an already materialized dependency cache.")
parser.add_argument("worktree", type=Path)
parser.add_argument("evidence", type=Path)
parser.add_argument("--lean-bin", type=Path, required=True)
parser.add_argument("--rounds", type=int, default=3)
args=parser.parse_args()
assert args.rounds > 0
root=args.worktree.resolve(); evidence=args.evidence.resolve(); evidence.mkdir(parents=True,exist_ok=True)
cache_root=root/".lake/refactor-cache/tv-yul"
cache_root.mkdir(parents=True,exist_ok=True)
proto_cache=cache_root/"prototype"; (proto_cache/"prototypes").mkdir(parents=True,exist_ok=True)
guard=Path(__file__).resolve().with_name("bounded.py")
# One namespace is resolved from the first matching LEAN_PATH root. Mirror all
# dependencies with symlinks, but materialize ancestors of replacement outputs.
def overlay(source,dest):
 dest.mkdir(parents=True,exist_ok=True)
 for path in source.iterdir():
  target=dest/path.name
  if target.exists():
   if target.is_dir() and not target.is_symlink(): overlay(path,target)
  else: target.symlink_to(path,target_is_directory=path.is_dir())
for mode in ["before","after"]:
 cache=cache_root/mode
 (cache/"Solidity/Yul/Compilation").mkdir(parents=True,exist_ok=True)
 overlay(root/".lake/build/lib/lean/Solidity",cache/"Solidity")
names=['NormalControl','NormalControlControls','NormalWordTransport','NormalWordTransportControls','NormalFramedTransport','NormalFramedTransportControls']
env=dict(os.environ,PATH=str(args.lean_bin.resolve())+':'+os.environ['PATH'],LEAN_NUM_THREADS='1')
results={}
for mode in ['before','after']:
 cache=cache_root/mode;env['LEAN_PATH']=str(cache)+':'+str(proto_cache)
 jobs=[]
 for name in (names if mode=='before' else ['NormalControl','NormalControlControls','NormalFramedTransport','NormalWordTransport','NormalWordTransportControls','NormalFramedTransportControls']):
  if mode=='after' and name=='NormalWordTransport': jobs.append(('prototype', ['lean','-j1','--tstack=131072','prototypes/TvYulBlock.lean','-o',str(proto_cache/'prototypes/TvYulBlock.olean')]))
  source='Solidity/Yul/Compilation/'+name+'.lean'; options=[]
  if mode=='after' and name=='NormalWordTransport':
   source='prototypes/shadow/'+source;options=['--root=prototypes/shadow']
  output=cache/('Solidity/Yul/Compilation/'+name+'.olean')
  if output.is_symlink(): output.unlink()
  jobs.append((name,['lean','-j1','--tstack=131072',*options,source,'-o',str(output)]))
 rounds=[]
 for repeat in range(args.rounds):
  records=[]
  for label,command in jobs:
   record=evidence/(mode+'-'+str(repeat)+'-'+label+'.json')
   with (record.with_suffix('.log')).open('w') as log:
    run=subprocess.run([sys.executable,str(guard),str(record),*command],cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT)
   result=json.loads(record.read_text());records.append(result)
   print(mode,repeat,label,result['exit'],result['seconds'],flush=True)
   if run.returncode:sys.exit(run.returncode)
  rounds.append(dict(seconds=sum(r['seconds'] for r in records),records=records))
 results[mode]=dict(rounds=rounds,median_seconds=statistics.median(r['seconds'] for r in rounds))
(evidence/'matched-kernel.json').write_text(json.dumps(results,indent=2)+'\n')
