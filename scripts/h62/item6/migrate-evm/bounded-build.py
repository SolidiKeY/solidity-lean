"""Serial private olean checks, hard-bounded by the caller's Docker cgroup.
This checks Lean files, not the full repository run-lean.sh gate.
"""
import argparse, hashlib, json, os, signal, subprocess, time
from pathlib import Path

GIB=1024**3

def resources():
    cg=Path("/sys/fs/cgroup")
    outer=Path("/run/outer-cgroup")
    if int((cg/"memory.max").read_text()) != 12*GIB or int((cg/"memory.swap.max").read_text()) != 0:
        raise RuntimeError("require hard 12 GiB/no-swap cgroup")
    available=int(next(x for x in Path("/proc/meminfo").read_text().splitlines() if x.startswith("MemAvailable:")).split()[1])*1024
    limit=int((outer/"memory.max").read_text()); used=int((outer/"memory.current").read_text())
    swap=int((outer/"memory.swap.current").read_text())
    return min(available,limit-used)>=4*GIB and swap==0

def group_rss(pgid):
    rss=0
    for item in Path("/proc").iterdir():
        if not item.name.isdigit(): continue
        try:
            if os.getpgid(int(item.name)) != pgid: continue
            lines=(item/"status").read_text().splitlines()
            rss += int(next(x for x in lines if x.startswith("VmRSS:")).split()[1])*1024
        except (FileNotFoundError,ProcessLookupError,StopIteration): pass
    return rss

def kill_group(child):
    try: os.killpg(child.pid,signal.SIGTERM)
    except ProcessLookupError: pass
    deadline=time.monotonic()+5
    while time.monotonic()<deadline:
        pid,status,usage=os.wait4(child.pid,os.WNOHANG)
        if pid:
            child.returncode=os.waitstatus_to_exitcode(status)
            try: os.killpg(child.pid,signal.SIGKILL)
            except ProcessLookupError: pass
            return usage
        time.sleep(.05)
    try: os.killpg(child.pid,signal.SIGKILL)
    except ProcessLookupError: pass
    _,status,usage=os.wait4(child.pid,0)
    child.returncode=os.waitstatus_to_exitcode(status)
    return usage

p=argparse.ArgumentParser()
p.add_argument("root",type=Path); p.add_argument("toolchain",type=Path)
p.add_argument("census",type=Path); p.add_argument("output",type=Path)
a=p.parse_args(); a.root=a.root.resolve(); a.output=a.output.resolve()
if a.output.exists(): raise SystemExit("refuse non-clean output directory")
if not resources(): raise SystemExit("resource preflight failed")
a.output.mkdir(parents=True)
data=json.loads(a.census.read_text()); env=os.environ.copy()
env.update(LEAN_NUM_THREADS="1", LEAN_PATH=str(a.output/"lib"), PATH=str(a.toolchain/"bin")+":"+env["PATH"])
lean=a.toolchain/"bin/lean"
versions={name:subprocess.check_output([str(a.toolchain/"bin"/name),"--version"],text=True).strip() for name in ("lean","lake")}
start=time.monotonic(); results=[]; stop=None; peak=0; exact_peak=0
try:
    for mod in data["order"]:
        source=a.root/data["modules"][mod]["path"]
        if hashlib.sha256(source.read_bytes()).hexdigest()!=data["modules"][mod]["sha256"]:
            stop="SOURCE_DRIFT:"+mod; break
        if not resources(): stop="RESOURCE_PREFLIGHT_STOP"; break
        dest=a.output/"lib"/(mod.replace(".","/")+".olean"); dest.parent.mkdir(parents=True,exist_ok=True)
        command=[str(lean),"--tstack=131072","-j1","-o",str(dest),str(source)]
        tick=time.monotonic(); rss=0; interrupted=None; usage=None; child=None
        events_before=Path("/sys/fs/cgroup/memory.events").read_text()
        with (a.output/(mod+".log")).open("w") as log:
            try:
                child=subprocess.Popen(command,cwd=a.root,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
                while True:
                    pid,status,usage=os.wait4(child.pid,os.WNOHANG)
                    if pid:
                        child.returncode=os.waitstatus_to_exitcode(status); break
                    rss=max(rss,group_rss(child.pid)); peak=max(peak,rss)
                    if not resources(): interrupted="RESOURCE_STOP"; break
                    if time.monotonic()-tick>300: interrupted="MODULE_300S_STOP"; break
                    time.sleep(.1)
            except BaseException as error:
                interrupted=type(error).__name__+":"+str(error)
            finally:
                if child is not None:
                    if child.returncode is None: usage=kill_group(child)
                    try: os.killpg(child.pid,signal.SIGKILL)
                    except ProcessLookupError: pass
        events_after=Path("/sys/fs/cgroup/memory.events").read_text()
        before=dict(line.split() for line in events_before.splitlines())
        after=dict(line.split() for line in events_after.splitlines())
        oom_delta=int(after["oom_kill"])-int(before["oom_kill"])
        if oom_delta: interrupted="CGROUP_OOM_STOP"
        rc=child.returncode if child is not None else -1
        exact=int(usage.ru_maxrss)*1024 if usage is not None else 0; exact_peak=max(exact_peak,exact)
        results.append({"module":mod,"command":command,"exit":rc,"wall_s":time.monotonic()-tick,"kernel_maxrss_bytes":exact,"sampled_group_peak_rss_bytes":rss,"stop":interrupted,"oom_kill_delta":oom_delta})
        (a.output/"progress.json").write_text(json.dumps(results,indent=2)+"\n")
        print(f"{mod}: exit={rc} wall={results[-1]['wall_s']:.2f}s",flush=True)
        if rc or interrupted: stop=interrupted or "ELABORATION_FAILURE:"+mod; break
except BaseException as error:
    stop=type(error).__name__+":"+str(error)
finally:
    summary={"cgroup_memory_peak_bytes":int(Path("/sys/fs/cgroup/memory.peak").read_text()),"versions":versions,"wall_s":time.monotonic()-start,"kernel_maxrss_bytes":exact_peak,"sampled_group_peak_rss_bytes":peak,"stop":stop,"checked":len(results),"required":len(data["order"]),"results":results,"settings":{"threads":1,"lean_args":["--tstack=131072","-j1"],"hard_cgroup_cap_bytes":12*GIB,"outer_reserve_bytes":4*GIB,"module_timeout_s":300,"cache":"clean private olean only; no per-master artifacts","swap_max_bytes":0,"peak_boundary":"wait4 max RSS per Lean child, sampled process-group aggregate"}}
    (a.output/"summary.json").write_text(json.dumps(summary,indent=2)+"\n")
raise SystemExit(0 if stop is None else 1)
