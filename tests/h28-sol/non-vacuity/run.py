#!/usr/bin/env python3
"""One locked command in the task-owned 12 GiB/no-swap Docker runtime."""
import argparse,fcntl,hashlib,json,os,pathlib,subprocess,sys,time
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent/'runtime'))
from workers import lean_workers
ROOT=pathlib.Path(__file__).resolve().parents[3]
p=argparse.ArgumentParser(); p.add_argument('--tag',required=True); p.add_argument('--evidence-dir',type=pathlib.Path); p.add_argument('command',nargs=argparse.REMAINDER); a=p.parse_args()
command=a.command[1:] if a.command[:1]==['--'] else a.command
if not command: p.error('command required')
if not a.tag.replace('-','').replace('_','').isalnum(): p.error('invalid tag')
container='h28-non-vacuity-runtime'
def dock(*args): return subprocess.check_output(['docker','exec',container,*args],text=True).strip()
lock=open('/tmp/solidity-lean-feature-groups-20261025/writer.lock','a')
fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
gate_head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
gate_branch=subprocess.check_output(['git','branch','--show-current'],cwd=ROOT,text=True).strip()
limit=dock('cat','/sys/fs/cgroup/memory.max','/sys/fs/cgroup/memory.swap.max').splitlines()
assert limit==[str(12*1024**3),'0'],limit
assert int(pathlib.Path('/sys/fs/cgroup/memory.max').read_text())==16*1024**3
def vm_headroom():
 # Only inactive file cache is treated as reclaimable; the hard job cap is unchanged.
 total=int(pathlib.Path('/sys/fs/cgroup/memory.max').read_text())
 current=int(pathlib.Path('/sys/fs/cgroup/memory.current').read_text())
 stats=dict(line.split() for line in pathlib.Path('/sys/fs/cgroup/memory.stat').read_text().splitlines())
 inactive=int(stats['inactive_file']); dirty=int(stats['file_dirty']); writeback=int(stats['file_writeback'])
 reclaimable=max(0,inactive-dirty-writeback)
 host_available=int(next(line.split()[1] for line in pathlib.Path('/proc/meminfo').read_text().splitlines() if line.startswith('MemAvailable:')))*1024
 cgroup_available=total-max(0,current-reclaimable)
 return dict(limit=total,current=current,inactive_file=inactive,file_dirty=dirty,file_writeback=writeback,reclaimable_file_estimate=reclaimable,host_available=host_available,cgroup_available=cgroup_available,available=min(cgroup_available,host_available))
cache_reclaims=[]
def reclaim_pages():
 # Read-only page-cache advice, never delete or modify an artifact.
 caches=[pathlib.Path('/workspace/.setup/cache/lake/artifacts'),pathlib.Path('/workspace/.setup/cache/.cache/lake/artifacts'),ROOT/'.lake/build']
 before=vm_headroom(); start_reclaim=time.monotonic(); count=0; failures=0
 for cache in caches:
  for candidate in cache.rglob('*'):
   if candidate.is_symlink() or not candidate.is_file():continue
   try:
    fd=os.open(candidate,os.O_RDONLY|os.O_NOFOLLOW)
    try:os.posix_fadvise(fd,0,0,os.POSIX_FADV_DONTNEED)
    finally:os.close(fd)
    count+=1
   except OSError:failures+=1
 after=vm_headroom()
 cache_reclaims.append(dict(operation='read-only POSIX_FADV_DONTNEED, no file/data mutation',roots=[str(x) for x in caches],files=count,failures=failures,before=before,after=after,elapsed_seconds=time.monotonic()-start_reclaim))
if vm_headroom()['available']<6*1024**3:reclaim_pages()
initial_headroom=vm_headroom()
assert initial_headroom['available']>=4*1024**3,initial_headroom
minimum_available=initial_headroom['available']
out=(a.evidence_dir or ROOT/'tests/h28-sol/non-vacuity/evidence').resolve()
assert out.is_relative_to(ROOT/'tests/h28-sol/non-vacuity'),'evidence outside owned scope'
out.mkdir(parents=True,exist_ok=True)
env_overrides={}
if command==['bash','scripts/coord-tools/gate.sh','full']:
 env_overrides['GATE_LOGS']=str(out.parent/'coord-gates')
log=out/(a.tag+'.log'); meta=out/(a.tag+'.json'); usage_file=out/(a.tag+'.rusage.json')
if log.exists() or meta.exists() or usage_file.exists(): raise SystemExit('refusing to overwrite evidence tag')
inputs={}
for value in command:
 candidate=None
 if value.startswith('+') and value.endswith(':olean'):
  logical=value[1:-6].replace('.','/')+'.lean'
  candidate=ROOT/logical
  if not candidate.is_file() and logical.startswith('Solidity/Assurance/NonVacuityH28/'):
   candidate=ROOT/'tests/h28-sol/non-vacuity/lean'/logical
 elif value.endswith('.lean') or value=='tests/h28-sol/non-vacuity/runtime/keysort': candidate=ROOT/value
 if candidate and candidate.is_file(): inputs[str(candidate.relative_to(ROOT))]=hashlib.sha256(candidate.read_bytes()).hexdigest()
if 'tests/h28-sol/non-vacuity/kernel.py' in command:
 for candidate in (ROOT/'tests/h28-sol/non-vacuity/lean/Solidity/Assurance/NonVacuityH28').glob('*.lean'):
  inputs[str(candidate.relative_to(ROOT))]=hashlib.sha256(candidate.read_bytes()).hexdigest()
 inputs['tests/h28-sol/non-vacuity/kernel.py']=hashlib.sha256((ROOT/'tests/h28-sol/non-vacuity/kernel.py').read_bytes()).hexdigest()
if command==['tests/h28-sol/non-vacuity/runtime/keysort']:
 inputs['Solidity/KeySort.lean']=hashlib.sha256((ROOT/'Solidity/KeySort.lean').read_bytes()).hexdigest()
measure_path=ROOT/'tests/h28-sol/non-vacuity/runtime/measure.py'
inputs[str(measure_path.relative_to(ROOT))]=hashlib.sha256(measure_path.read_bytes()).hexdigest()
workers_path=ROOT/'tests/h28-sol/non-vacuity/runtime/workers.py'
inputs[str(workers_path.relative_to(ROOT))]=hashlib.sha256(workers_path.read_bytes()).hexdigest()
wrapper_command=['python3',str(measure_path),str(usage_file),*command]
runner_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()
def events(): return dict((k,int(v)) for k,v in (line.split() for line in dock('cat','/sys/fs/cgroup/memory.events').splitlines()))
initial_memory_events=events()
start=time.monotonic(); peak_rss=0; worker_snapshots=[]; stop=None; last_reclaim=start
with log.open('w') as f:
 child=subprocess.Popen(['docker','exec',*[x for k,v in env_overrides.items() for x in ['-e',k+'='+v]],container,*wrapper_command],stdout=f,stderr=subprocess.STDOUT)
 while child.poll() is None:
  try:
   ps=dock('ps','-eo','rss,args','--no-headers'); rows=ps.splitlines()
   peak_rss=max(peak_rss,sum(int(x.split(None,1)[0])*1024 for x in rows))
   workers=lean_workers(ps)
   if len(workers)>1: stop='more than one heavy Lean worker observed'
   if workers and (not worker_snapshots or workers!=worker_snapshots[-1]): worker_snapshots.append(workers)
   headroom=vm_headroom(); minimum_available=min(minimum_available,headroom['available'])
   if headroom['available']<4*1024**3: stop='4 GiB VM working-set reserve guard'
   if stop is None and headroom['available']<6*1024**3 and time.monotonic()-last_reclaim>=30:
    reclaim_pages();last_reclaim=time.monotonic();headroom=vm_headroom()
   minimum_available=min(minimum_available,headroom['available'])
   if headroom['available']<4*1024**3: stop='4 GiB VM working-set reserve guard'
  except (OSError,ValueError,subprocess.CalledProcessError): stop='resource observation failed'
  if stop:
   subprocess.run(['docker','stop','-t','2',container],stdout=f,stderr=subprocess.STDOUT); child.wait(); break
  time.sleep(1)
 elapsed=time.monotonic()-start
 try: peak_cgroup=int(dock('cat','/sys/fs/cgroup/memory.peak'))
 except subprocess.CalledProcessError: peak_cgroup=None
for name,digest in inputs.items():
 if hashlib.sha256((ROOT/name).read_bytes()).hexdigest()!=digest: stop='source input changed during gate'
try: final_memory_events=events()
except subprocess.CalledProcessError: final_memory_events=None
rusage=json.loads(usage_file.read_text()) if usage_file.exists() else None
if subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()!=gate_head or subprocess.check_output(['git','branch','--show-current'],cwd=ROOT,text=True).strip()!=gate_branch: stop='committed head/branch changed during gate'
record=dict(git_head=gate_head,git_branch=gate_branch,env_overrides=env_overrides,cache_reclaims=cache_reclaims,wrapper_command=wrapper_command,rusage=rusage,rusage_file=str(usage_file.relative_to(ROOT)),rusage_sha256=hashlib.sha256(usage_file.read_bytes()).hexdigest() if usage_file.exists() else None,runner_sha256=runner_sha256,initial_memory_events=initial_memory_events,final_memory_events=final_memory_events,headroom_method='estimated min(host MemAvailable, cgroup max-current+max(0,inactive_file-dirty-writeback))',initial_vm_headroom=initial_headroom,minimum_vm_available_bytes=minimum_available,input_sha256=inputs,log_sha256=hashlib.sha256(log.read_bytes()).hexdigest(),command=command,container=container,exit=child.returncode,elapsed_seconds=elapsed,sampled_peak_aggregate_rss_bytes=peak_rss,cgroup_memory_peak_bytes=peak_cgroup,limits=limit,stop=stop,worker_snapshots=worker_snapshots)
meta.write_text(json.dumps(record,indent=2)+'\n'); print(json.dumps({k:v for k,v in record.items() if k!='worker_snapshots'})); raise SystemExit(child.returncode or (1 if stop else 0))
