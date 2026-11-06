#!/usr/bin/env python3
"""Measured single-job runner, executed inside the fixed Docker cgroup."""
import json,os,pathlib,signal,subprocess,sys,time
label=sys.argv[1];limit=int(sys.argv[2]);cmd=sys.argv[3:]
assert limit<=300 and cmd
root=pathlib.Path('tests/fullscope-20261104/vt1/ImportFollowup/evidence');root.mkdir(parents=True,exist_ok=True)
assert pathlib.Path('/sys/fs/cgroup/memory.max').read_text().strip()=='12884901888'
assert pathlib.Path('/sys/fs/cgroup/memory.swap.max').read_text().strip()=='0'
def available():
 return next(int(l.split()[1])*1024 for l in pathlib.Path('/proc/meminfo').read_text().splitlines() if l.startswith('MemAvailable:'))
def sample():
 rss=0;leans=0
 for p in pathlib.Path('/proc').glob('[0-9]*/status'):
  try:
   rss+=next((int(l.split()[1])*1024 for l in p.read_text().splitlines() if l.startswith('VmRSS:')),0)
   raw=(p.parent/'cmdline').read_bytes().split(b'\0')[0]
   leans+=int(raw.rsplit(b'/',1)[-1]==b'lean')
  except (FileNotFoundError,ProcessLookupError,PermissionError):pass
 return rss,leans
assert available()>=4*1024**3
spent=0
for previous in root.glob('*.json'):
 try:
  record=json.loads(previous.read_text())
  if isinstance(record,dict):spent+=record.get('wall_seconds',0)
 except (ValueError,TypeError):pass
assert spent<14400,'aggregate build window exhausted'
index=1
while (root/f'{label}-{index}.json').exists():index+=1
log=root/f'{label}-{index}.log';start=time.monotonic();peak=0;maximum=0;reason=None
with log.open('w') as out:
 proc=subprocess.Popen(cmd,stdout=out,stderr=subprocess.STDOUT,start_new_session=True)
 while proc.poll() is None:
  rss,leans=sample();peak=max(peak,rss);maximum=max(maximum,leans)
  if leans>1 or available()<4*1024**3 or time.monotonic()-start>limit:
   reason='serial/headroom/time guard';os.killpg(proc.pid,signal.SIGTERM)
   try:proc.wait(timeout=5)
   except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);proc.wait()
   break
  time.sleep(.02)
result=dict(command=cmd,exit=proc.returncode,wall_seconds=time.monotonic()-start,aggregate_peak_rss_bytes=peak,max_lean_processes=maximum,stop_reason=reason,above_60_seconds=time.monotonic()-start>60,log=str(log))
(root/f'{label}-{index}.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
print(log.read_text()[-5000:],flush=True)
raise SystemExit(proc.returncode if proc.returncode else (1 if reason else 0))
