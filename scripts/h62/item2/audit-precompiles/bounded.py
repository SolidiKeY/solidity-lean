#!/usr/bin/env python3
"""Run a serial bounded command and record exit, wall time and child RSS."""
import argparse, fcntl, hashlib, json, os, pathlib, re, resource, signal, subprocess, time
p=argparse.ArgumentParser()
p.add_argument('--evidence',type=pathlib.Path,required=True)
p.add_argument('--seconds',type=int,default=300)
p.add_argument('command',nargs=argparse.REMAINDER)
a=p.parse_args()
cmd=a.command[1:] if a.command[:1]==['--'] else a.command
if not cmd: p.error('command required')
lock=open('/tmp/solidity-lean-feature-groups-20261025/writer.lock','a')
fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
if len(pathlib.Path('/proc/swaps').read_text().splitlines())!=1:
 raise SystemExit('RESOURCE_BLOCK: swap enabled')
mem={s.split(':')[0]:int(s.split()[1]) for s in pathlib.Path('/proc/meminfo').read_text().splitlines() if s.startswith('MemAvailable:')}
if mem['MemAvailable']<16*1024*1024:
 raise SystemExit('RESOURCE_BLOCK: 12GiB cap + 4GiB reserve unavailable')
def limits():
 resource.setrlimit(resource.RLIMIT_AS,(12*1024**3,12*1024**3))
 resource.setrlimit(resource.RLIMIT_CORE,(0,0))
a.evidence.parent.mkdir(parents=True,exist_ok=True)
env=dict(os.environ,LEAN_NUM_THREADS='1')
inputs={}
def record(path):
 path=path.resolve()
 if str(path) in inputs or not path.is_file(): return
 raw=path.read_bytes()
 inputs[str(path)]=hashlib.sha256(raw).hexdigest()
 if path.suffix=='.lean':
  for module in re.findall(r'^import[ \t]+(Solidity\.[^ \t\n]+)',raw.decode(),re.M):
   record(pathlib.Path.cwd()/(module.replace('.','/')+'.lean'))
for arg in cmd:
 if arg.endswith(('.lean','.toml')): record(pathlib.Path(arg))
start=time.monotonic()
with a.evidence.with_suffix('.log').open('w') as log:
 child=subprocess.Popen(cmd,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True,preexec_fn=limits)
 timeout=False
 resource_stop=None
 peak_group_rss=0
 minimum_available=mem['MemAvailable']*1024
 while child.poll() is None:
  available=int(next(s.split()[1] for s in pathlib.Path('/proc/meminfo').read_text().splitlines() if s.startswith('MemAvailable:')))*1024
  minimum_available=min(minimum_available,available)
  rss=0
  lean_workers=0
  for entry in pathlib.Path('/proc').iterdir():
   if not entry.name.isdigit(): continue
   try:
    if os.getpgid(int(entry.name))!=child.pid: continue
    status=(entry/'status').read_text()
    rss+=sum(int(line.split()[1])*1024 for line in status.splitlines() if line.startswith('VmRSS:'))
    if (entry/'comm').read_text().strip()=='lean': lean_workers+=1
   except (FileNotFoundError,ProcessLookupError,PermissionError): pass
  peak_group_rss=max(peak_group_rss,rss)
  if available<4*1024**3: resource_stop='available reserve below 4GiB'
  if rss>12*1024**3: resource_stop='aggregate RSS above 12GiB'
  if lean_workers>1: resource_stop='more than one Lean worker'
  timeout=time.monotonic()-start>a.seconds
  if timeout or resource_stop: break
  time.sleep(0.25)
 if timeout or resource_stop:
  os.killpg(child.pid,signal.SIGTERM)
  try: child.wait(timeout=5)
  except subprocess.TimeoutExpired: os.killpg(child.pid,signal.SIGKILL); child.wait()
  rc=124 if timeout else 70
 else: rc=child.returncode
inputs_unchanged=all(pathlib.Path(p).is_file() and hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()==h for p,h in inputs.items())
if not inputs_unchanged: rc=71
result=dict(input_sha256=inputs,inputs_unchanged=inputs_unchanged,command=cmd,cwd=os.getcwd(),exit=rc,timeout=timeout,resource_stop=resource_stop,aggregate_peak_rss_bytes=peak_group_rss,minimum_available_bytes=minimum_available,wall_seconds=time.monotonic()-start,maxrss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,lean_num_threads=1,address_space_cap_bytes=12*1024**3,swap='disabled',reserve_bytes=4*1024**3)
a.evidence.with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
raise SystemExit(rc)
