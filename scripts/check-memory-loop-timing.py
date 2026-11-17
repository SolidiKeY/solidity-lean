#!/usr/bin/env python3
"""Freshly check the entire original Derived17 workload. Wrap in a 300s guard.
Existing prerequisite Lake setups are required; group outputs never reused.

Speed budget: heartbeats, the same count on every machine (H1076). Each module is
checked by scripts/heartbeats/replay/Replay.lean, which does what
`lean --setup SETUP SOURCE -o OLEAN -c C` did, with Elab.async=false (kernel
checking is counted), one thread and a 128 MiB stack, and counts heartbeats per
command like scripts/heartbeats/collect.sh; its wall time matches `lean`. It is
compiled once per source and toolchain into .lake/build/heartbeats-replay/
(about 15 s, before the timed workload starts).

Ratchet: scripts/heartbeats/replay/baseline.json holds every module's total, its
commands of at least 100 units, and the workload total as the entry
`workload:fresh-original-Derived17`; scripts/heartbeats/collect.d/ratchet.py
compares them. An entry fails when it grows by more than --tolerance percent
(default 2) and by more than 1 unit; a decrease, a new or a removed entry only
prints. A ratchet failure, like the seconds backstop (--budget: 300 locally, CI
passes 600, H116), makes the exit status and the results' exit_code 1.
Regenerate the baseline on the merged head (or the merge base) and check it in:
  python3 scripts/check-memory-loop-timing.py --write --output DIR --results FILE
--write replaces the file, only when every module checked without errors.

--results keeps every earlier field. New: per check `heartbeats`,
`importHeartbeats`, `heartbeatsFile` (DIR/MODULE.heartbeats.json, the collector's
shape); at the top `heartbeats` (workload total), `heartbeatBaseline`,
`heartbeatTolerancePercent` and `heartbeatRatchet` (mode, exit_code, failures,
report). Heartbeats are in maxHeartbeats units (raw / 1000).
"""
import argparse, pathlib, subprocess, json, time, hashlib, os, resource, shutil, sys, tempfile
r=pathlib.Path(__file__).resolve().parent.parent;hb=r/'scripts/heartbeats'
p=argparse.ArgumentParser();p.add_argument('--output',required=True);p.add_argument('--results',required=True);p.add_argument('--budget',type=float,default=300.0,help='seconds; 300 is the local/VM budget, CI passes a runner-calibrated value (H116)')
p.add_argument('--baseline',default=str(hb/'replay/baseline.json'),help='heartbeat baseline (default scripts/heartbeats/replay/baseline.json)')
p.add_argument('--tolerance',type=float,default=2.0,help='percent a module, recorded declaration or the workload may exceed its baseline heartbeats (default 2)')
p.add_argument('--write',action='store_true',help='regenerate --baseline from this run instead of comparing (on the merged head)');a=p.parse_args()
d=pathlib.Path(a.output);d.mkdir(exist_ok=False)
modules=['Solidity.Calculus.MemoryLoopReplay']+['Solidity.TestSuite.MemoryLoopReplay.'+kind+f'{i:02}' for kind in ['Discover','Assemble'] for i in range(10)]+['Solidity.TestSuite.Derived17MemoryLoop','Solidity.TestSuite.MemoryLoopReplay.Refusals','Solidity.TestSuite.Derived17']
WORKLOAD='workload:fresh-original-Derived17';MIN_UNITS=100  # smaller commands count only in their module's total

def driver():
 """Compile the replay driver once per (source, toolchain) into .lake/build; not part of the timed workload."""
 src=hb/'replay/Replay.lean';ver=subprocess.run(['lean','--version'],capture_output=True,text=True,check=True).stdout
 key=hashlib.sha256(src.read_bytes()+ver.encode()).hexdigest()[:16];out=r/'.lake/build/heartbeats-replay'/key/'replay'
 if not out.exists():
  tmp=pathlib.Path(tempfile.mkdtemp(dir=r/'.lake/build'))
  try:
   subprocess.run(['lean',str(src),'-c',str(tmp/'Replay.c')],cwd=r,check=True)
   # -rdynamic: the interpreter runs the checked modules' own elaborators against this binary's Lean
   subprocess.run(['leanc',str(tmp/'Replay.c'),'-o',str(tmp/'replay'),'-rdynamic'],cwd=r,check=True)
   out.parent.mkdir(parents=True,exist_ok=True);os.replace(tmp/'replay',out)
  finally:shutil.rmtree(tmp,ignore_errors=True)
 return out
(r/'.lake/build').mkdir(parents=True,exist_ok=True);exe=driver()

def stack():
 # Elab.async=false elaborates on the main thread: give it the library's 128 MiB (collect.sh).
 try:resource.setrlimit(resource.RLIMIT_STACK,(128*1024*1024,resource.getrlimit(resource.RLIMIT_STACK)[1]))
 except (ValueError,OSError):pass

rows=[];arts={};start=time.monotonic();env=os.environ.copy();env['LEAN_NUM_THREADS']='1';hbs={};ratchet=None
def save(code,seconds=None):
 total=round(sum(x['heartbeats'] for x in hbs.values()),3) if hbs else None
 pathlib.Path(a.results).write_text(json.dumps(dict(kind='fresh-original-Derived17-workload',budgetSeconds=a.budget,exit_code=code,seconds=time.monotonic()-start if seconds is None else seconds,expectedModules=modules,checks=rows,
  heartbeats=total,heartbeatBaseline=os.path.relpath(a.baseline,r),heartbeatTolerancePercent=a.tolerance,heartbeatRatchet=ratchet),indent=2)+'\n')
save(None)
for module in modules:
 path=module.replace('.','/');sf=r/('.lake/build/ir/'+path+'.setup.json')
 # A module fetched from Lake's artifact cache has no .setup.json in .lake/build; ask Lake for it.
 setup=json.loads(sf.read_text() if sf.exists() else subprocess.run(['lake','setup-file',path+'.lean'],cwd=r,check=True,capture_output=True,text=True).stdout);setup['importArts'].update(arts)
 sp=d/(module+'.setup.json');sp.write_text(json.dumps(setup));source=r/(path+'.lean');log=d/(module+'.log');out=d/(module+'.olean');hj=d/(module+'.heartbeats.json')
 cmd=[str(exe),str(sp),str(source),str(out),str(d/(module+'.c')),str(hj)]
 (d/(module+'.source.lean')).write_bytes(source.read_bytes())
 t=time.monotonic()
 with log.open('wb') as stream:code=subprocess.run(cmd,cwd=r,env=env,stdout=stream,stderr=subprocess.STDOUT,preexec_fn=stack).returncode
 seconds=time.monotonic()-t;h=json.loads(hj.read_text()) if hj.exists() else None
 if h:hbs[module]=h
 rows.append(dict(module=module,source=str(source),sourceSha256=hashlib.sha256(source.read_bytes()).hexdigest(),command=cmd,exit_code=code,seconds=seconds,log=str(log),output=str(out),fresh=True,
  heartbeats=h and h['heartbeats'],importHeartbeats=h and h['import_heartbeats'],heartbeatsFile=str(hj) if h else None));save(code if code else None)
 print(module,code,rows[-1]['seconds'],rows[-1]['heartbeats'],flush=True)
 if code:raise SystemExit(code)
 arts[module]=[str(out)]
seconds=time.monotonic()-start;over=seconds>a.budget

# Heartbeat ratchet (scripts/heartbeats/collect.d/ratchet.py): every module plus the workload total as one more entry.
run=d/'heartbeats.jsonl'
with run.open('w') as f:
 for m in modules:f.write(json.dumps(hbs[m])+'\n')
 f.write(json.dumps(dict(module=WORKLOAD,heartbeats=round(sum(x['heartbeats'] for x in hbs.values()),3),errors=0,commands=[]))+'\n')
rt=str(hb/'collect.d/ratchet.py')
if a.write:
 new=d/'baseline.json';new.write_text(json.dumps(dict(min_units=MIN_UNITS,modules={})))
 rc=subprocess.run([sys.executable,rt,'write',str(new),str(run)]).returncode
 if rc==0:shutil.copyfile(new,a.baseline)
 ratchet=dict(mode='write',exit_code=rc,failures=[])
else:
 res=subprocess.run([sys.executable,rt,'check',a.baseline,str(run),'--tolerance',str(a.tolerance)],capture_output=True,text=True)
 sys.stdout.write(res.stdout);sys.stderr.write(res.stderr)
 ratchet=dict(mode='check',exit_code=res.returncode,failures=[l[5:] for l in res.stdout.splitlines() if l.startswith('FAIL ')],report=res.stdout.splitlines())
print(f"heartbeats: workload {sum(x['heartbeats'] for x in hbs.values()):.3f} ({'written to' if a.write else 'checked against'} {os.path.relpath(a.baseline,r)}, {ratchet['exit_code'] and 'FAILED' or 'ok'}); seconds {seconds:.1f} of {a.budget}",flush=True)
final_code=1 if over or ratchet['exit_code'] else 0
save(final_code,seconds)
raise SystemExit(final_code)
