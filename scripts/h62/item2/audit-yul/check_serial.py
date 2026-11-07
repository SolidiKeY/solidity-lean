#!/usr/bin/env python3
"""Fresh source checks, serial bounded Lean. Does not replace run-lean.sh.
Each process group is monitored; resource stops/timeouts are logged failures.
No artifact cache from another tree/toolchain is used.
"""
import argparse, fcntl, hashlib, json, os, pathlib, re, resource, signal, subprocess, time
GiB=1024**3
ap=argparse.ArgumentParser();ap.add_argument('--evidence',type=pathlib.Path,required=True);ap.add_argument('--lean',type=pathlib.Path,required=True);ap.add_argument('--dependency-lib',type=pathlib.Path);ap.add_argument('--run',action='store_true');ap.add_argument('targets',nargs='+');args,run_args=ap.parse_known_args()
root=pathlib.Path.cwd();ev=args.evidence.resolve();ev.mkdir(parents=True,exist_ok=True)
lock=open('/tmp/solidity-lean-feature-groups-20261025/writer.lock','a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
print(subprocess.check_output(['git','status','--short'],text=True),flush=True)
if pathlib.Path('/proc/swaps').read_text().strip().count('\n'):raise SystemExit('swap must be disabled')
lib=ev/'lib';lib.mkdir(exist_ok=True);env=os.environ.copy();env['LEAN_NUM_THREADS']='1';env['LEAN_PATH']=str(lib)
if args.dependency_lib:
 dependency_lib=args.dependency_lib.resolve()
 # Lean resolves a package prefix from one search root. Materialize a single
 # union of this run's fresh outputs and explicitly supplied fresh dependencies.
 for source in dependency_lib.rglob('*.olean'):
  destination=lib/source.relative_to(dependency_lib)
  if not destination.exists():
   destination.parent.mkdir(parents=True,exist_ok=True);destination.symlink_to(source)

# The invoking shell need not have a Lean toolchain on PATH.
env['PATH']=str(args.lean.resolve().parent)+os.pathsep+env['PATH']
log=ev/'commands.jsonl';seen=set();active=set()
cgroup=pathlib.Path('/sys/fs/cgroup')
def available():
 host=int(re.search(r'MemAvailable:\s+(\d+)',pathlib.Path('/proc/meminfo').read_text())[1])*1024
 cap=(cgroup/'memory.max').read_text().strip()
 if cap!='max':host=min(host,int(cap)-int((cgroup/'memory.current').read_text()))
 return host

def swap_active():
 if pathlib.Path('/proc/swaps').read_text().strip().count('\n'):return True
 swap_current=cgroup/'memory.swap.current'
 return swap_current.exists() and int(swap_current.read_text())>0

def group_memory(pgid):
 total=0;virtual=0
 for p in pathlib.Path('/proc').glob('[0-9]*/stat'):
  try:
   values=p.read_text().rsplit(')',1)[1].split()
   if int(values[2])==pgid:
    total+=int(values[21])*os.sysconf('SC_PAGE_SIZE');virtual+=int(values[20])
  except (OSError,ValueError,IndexError):pass
 return total,virtual

def run(cmd,key,source):
 initial=available();cap=min(12*GiB,initial-4*GiB)
 if cap<GiB:raise SystemExit('insufficient room for child plus 4GiB reserve')
 # The assigned budget is resident memory. RLIMIT_AS also charges reserved
 # thread stacks, and is not an RSS bound (repository resource policy).
 # Keep Lean's heap cap, VM cgroup hard cap, group RSS and reserve monitors.
 def limits():resource.setrlimit(resource.RLIMIT_CORE,(0,0))
 lp=ev/(key.replace('/','__')+'.attempt'+str(sum(1 for _ in log.open())+1 if log.exists() else 1)+'.log');start=time.monotonic();reason=None;peak=0;peak_virtual=0
 print('CHECK '+key,flush=True)
 with lp.open('w') as output:
  proc=subprocess.Popen(cmd,env=env,text=True,stdout=output,stderr=subprocess.STDOUT,preexec_fn=limits,start_new_session=True)
  while proc.poll() is None:
   rss,virtual=group_memory(proc.pid)
   peak=max(peak,rss);peak_virtual=max(peak_virtual,virtual)
   if swap_active():reason='resource_stop_swap_enabled_or_used'
   elif available()<4*GiB:reason='resource_stop_4GiB_reserve'
   elif peak>cap:reason='resource_stop_group_RSS'
   elif time.monotonic()-start>1800:reason='timeout_1800s'
   if reason:
    os.killpg(proc.pid,signal.SIGKILL);proc.wait();break
   time.sleep(0.2)
  code=proc.wait()
 elapsed=time.monotonic()-start
 row=dict(command=cmd,exit=code,stop_reason=reason,seconds=elapsed,source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),log=str(lp),available_before=initial,resident_budget=cap,inherited_address_space_limit=resource.getrlimit(resource.RLIMIT_AS),peak_group_rss=peak,peak_group_virtual=peak_virtual)
 with log.open('a') as f:f.write(json.dumps(row,sort_keys=True)+'\n')
 print(f'EXIT {code} {elapsed:.3f}s {lp}',flush=True)
 if code or reason:raise SystemExit(code or 1)

def compile_file(path):
 path=pathlib.Path(path);key=str(path)
 if key in seen:return
 if key in active:raise SystemExit('cyclic imports: '+key)
 active.add(key)
 for dep in re.findall(r'^import\s+(\S+)',path.read_text(),re.M):
  module_path=dep.replace('«','').replace('»','').replace('.','/')+'.lean'
  dp=root/module_path
  if dp.exists():
   # Optional dependency lib must be from a separately logged fresh build.
   if args.dependency_lib and (args.dependency_lib/pathlib.Path(module_path).with_suffix('.olean')).exists():continue
   compile_file(dp.relative_to(root))
 active.remove(key)
 out=lib/path.with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
 if out.is_symlink():out.unlink()  # Never overwrite an earlier evidence library through a symlink.
 cmd=[str(args.lean.resolve()),'-j1','--tstack=131072','-M=11000','--root='+str(root),'-o',str(out),str(path)]
 run(cmd,key,path);seen.add(key)
if args.run:
 if len(args.targets)!=1:raise SystemExit('--run requires one source file')
 path=pathlib.Path(args.targets[0]);run([str(args.lean.resolve()),'-j1','--tstack=131072','-M=11000','--run',str(path),*run_args],str(path)+'-run',path)
else:
 if run_args:raise SystemExit('unexpected args: '+str(run_args))
 for target in args.targets:compile_file(target)
print('SERIAL_FILE_CHECK_PASS (not RUNTIME_GATE_PASS)',flush=True)
