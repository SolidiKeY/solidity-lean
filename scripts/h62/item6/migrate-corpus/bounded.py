#!/usr/bin/env python3
"""Run one command under the repository lock; monitor the entire task descendant tree.
Monitor 12 GiB aggregate RSS and 4 GiB cgroup/host headroom; require no swap.
The VM has a hard 16 GiB cgroup cap. Virtual-address reservations are not RSS.
Sampled aggregate RSS is a lower bound on peaks, not a hard 12 GiB group cap.
Each Lean invocation must separately carry -j1 (use serial-toolchain.py).
"""
import argparse, ctypes, fcntl, hashlib, json, os, pathlib, signal, subprocess, time, tomllib
GIB=1024**3
p=argparse.ArgumentParser(); p.add_argument("--out",type=pathlib.Path,required=True); p.add_argument("--timeout",type=float,default=0); p.add_argument("--benchmark-config",type=pathlib.Path); p.add_argument("command",nargs=argparse.REMAINDER); a=p.parse_args()
cmd=a.command[1:] if a.command[:1]==["--"] else a.command
assert cmd
lock=open("/tmp/solidity-lean-feature-groups-20261025/writer.lock","a")
fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
subprocess.run(["git","status","--short"],check=True)
a.out.mkdir(parents=True,exist_ok=False)
assert int(pathlib.Path("/proc/meminfo").read_text().split("SwapTotal:")[1].split()[0])==0,"active swap forbidden"
cap=int(pathlib.Path("/sys/fs/cgroup/memory.max").read_text())
available=int(pathlib.Path("/proc/meminfo").read_text().split("MemAvailable:")[1].split()[0])*1024
current=int(pathlib.Path("/sys/fs/cgroup/memory.current").read_text())
assert min(available,cap-current)>=4*GIB,"insufficient preflight reserve"
benchmark = None
if a.benchmark_config:
    config=tomllib.loads(a.benchmark_config.read_text())
    assert cmd[-2:]==["build","SolidityCorpus"] and "--no-cache" in cmd
    assert "-f" in cmd and pathlib.Path(cmd[cmd.index("-f")+1]).resolve()==a.benchmark_config.resolve()
    assert config.get("enableArtifactCache") is False
    build=pathlib.Path(config["buildDir"])
    assert build.is_absolute() and not build.exists(), "benchmark requires absent output directory"
    base="c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
    paths=subprocess.check_output(["git","ls-tree","-r","--name-only",base],text=True).splitlines()
    digest=hashlib.sha256()
    for path in paths:
        h=hashlib.sha256()
        with open(path,"rb") as src:
            for chunk in iter(lambda:src.read(1024*1024),b""): h.update(chunk)
        digest.update(path.encode()+b"\0"+h.digest())
    config.pop("buildDir")
    benchmark=dict(schema="corpus-clean-v1",base=base,targets=["SolidityCorpus"],clean=True,
                   cache_policy="absent-output;artifact-cache-disabled;--no-cache",
                   input_tree_sha256=digest.hexdigest(),
                   config_policy_sha256=hashlib.sha256(json.dumps(config,sort_keys=True).encode()).hexdigest())
    (a.out/"benchmark.json").write_text(json.dumps(benchmark,indent=2)+"\n")
stopping = []
def interrupted(signum, _frame):
    stopping.append(signum)
signal.signal(signal.SIGTERM, interrupted)
signal.signal(signal.SIGINT, interrupted)
# MCP may create new sessions: adopt orphan descendants and follow ancestry,
# not just one process group. Start times prevent PID-reuse confusion.
if ctypes.CDLL(None).prctl(36,1,0,0,0)!=0:
    raise RuntimeError("cannot establish child subreaper")
known={}; driver=os.getpid(); proc=None
def members():
    rows={}
    for d in pathlib.Path("/proc").iterdir():
        if not d.name.isdigit():continue
        try:
            f=(d/"stat").read_text().rsplit(")",1)[1].split()
            rows[int(d.name)]=(int(f[1]),int(f[2]),int(f[19]),int(f[21])*os.sysconf("SC_PAGE_SIZE"),f[0])
        except (OSError,ValueError,IndexError):pass
    mine={pid for pid,r in rows.items() if r[0]==driver or (proc and pid==proc.pid and proc.poll() is None) or known.get(pid)==r[2]}
    while True:
        more={pid for pid,r in rows.items() if r[0] in mine}
        if more<=mine:break
        mine.update(more)
    for pid in mine:known[pid]=rows[pid][2]
    return {pid:rows[pid] for pid in mine if pid!=driver}
def signal_tree(sig):
    rows=members()
    for group in {r[1] for r in rows.values()}:
        if group!=os.getpgrp():
            try:os.killpg(group,sig)
            except ProcessLookupError:pass
    for pid in rows:
        try:os.kill(pid,sig)
        except ProcessLookupError:pass
start=time.monotonic(); peak=0; reason=None
with (a.out/"output.log").open("w") as log:
    proc=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT,start_new_session=True,env=dict(os.environ,LEAN_NUM_THREADS="1"))
    try:
        while proc.poll() is None:
            if stopping:
                reason=f"INTERRUPTED: signal {stopping[0]}";break
            peak=max(peak,sum(r[3] for r in members().values()))
            available=int(pathlib.Path("/proc/meminfo").read_text().split("MemAvailable:")[1].split()[0])*1024
            current=int(pathlib.Path("/sys/fs/cgroup/memory.current").read_text())
            if peak>12*GIB or min(available,cap-current)<4*GIB:
                reason="RESOURCE_STOP: sampled RSS or 4 GiB reserve";break
            if a.timeout and time.monotonic()-start>a.timeout:
                reason="TIMEOUT_STOP";break
            time.sleep(.2)
        if stopping and reason is None:reason=f"INTERRUPTED: signal {stopping[0]}"
    except BaseException as exc:
        reason=f"MONITOR_OR_INTERRUPT_STOP: {type(exc).__name__}: {exc}"
    finally:
        signal.signal(signal.SIGTERM,signal.SIG_IGN);signal.signal(signal.SIGINT,signal.SIG_IGN)
        signal_tree(signal.SIGTERM)
        try:proc.wait(timeout=5)
        except subprocess.TimeoutExpired:pass
        signal_tree(signal.SIGKILL);code=proc.wait()
        deadline=time.monotonic()+5
        while True:
            try:
                while os.waitpid(-1,os.WNOHANG)[0]:pass
            except ChildProcessError:pass
            remaining={pid:r for pid,r in members().items() if r[4]!="Z"}
            if not remaining:break
            if time.monotonic()>deadline:
                reason=reason or "CLEANUP_FAILURE: live task descendants";break
            signal_tree(signal.SIGKILL);time.sleep(.05)

result=dict(benchmark=benchmark,per_process_as_cap_bytes=None,command=cmd,exit=(124 if reason else code),child_exit=code,wall_seconds=time.monotonic()-start,peak_aggregate_rss_bytes=peak,resource_stop=reason,threads=1,rss_stop_threshold_bytes=12*GIB,hard_vm_cap_bytes=cap,reserve_bytes=4*GIB,swap_total_bytes=0)
(a.out/"result.json").write_text(json.dumps(result,indent=2)+"\n"); print(json.dumps(result)); raise SystemExit(124 if reason else (code if code>=0 else 128-code))
