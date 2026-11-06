#!/usr/bin/env python3
"""Serial clean import-closure measurements in an isolated Docker cgroup.
No artifact cache, no tracked config edits, no systemd, no budget increases.
A failure is evidence, never a proof of compatibility or a timing comparison.
"""
import fcntl, hashlib, importlib.util, json, os, shlex, subprocess, sys, time
from pathlib import Path
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[4]
EVIDENCE=Path("/workspace/migrate-roadmap-evidence")
IMAGE="ubuntu@sha256:fe81560990fae86dc4743202b2cb4d3df98d0bcf949173cecef15ce1127ef852"
DOCKER=["docker","--host=unix:///var/run/docker.sock"]
def bounded_control(command, *, env, **kwargs):
    """A daemon failure cannot indefinitely block the resource observer."""
    kwargs.setdefault("timeout",2)
    try:return subprocess.run(command,env=env,**kwargs)
    except subprocess.TimeoutExpired:
        return subprocess.CompletedProcess(command,124,stdout="" if kwargs.get("text") else None,stderr="Docker control timeout")
def main():
    if len(sys.argv) not in (3,4) or sys.argv[1] not in ("old","new") or sys.argv[2] not in ("prerequisite","baseline","after","fixtures","api","matrix","classify"):
        raise SystemExit("usage: build.py old|new prerequisite|baseline|after")
    version,phase=sys.argv[1:3]
    if (phase=="api") != (len(sys.argv)==4):raise SystemExit("api requires a successful full-closure result.json; other modes take no extra argument")
    lock=open("/tmp/solidity-lean-feature-groups-20261025/writer.lock","a")
    fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    subprocess.run(["git","status","--short"],cwd=ROOT,check=True)
    subprocess.run(["git","merge-base","--is-ancestor","c6f550e281a7e5affa9a99bc2cdaed556dec00e4","HEAD"],cwd=ROOT,check=True)
    spec=importlib.util.spec_from_file_location("census",Path(__file__).with_name("census.py"))
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
    c=mod.census(ROOT)
    g=mod.graph(ROOT)
    inputs=[g.source(m) for m in c["closure"]]+[ROOT/"lakefile.toml",ROOT/"lean-toolchain",ROOT/"run-lean.sh",ROOT/"scripts/v08-build-graph.py",ROOT/"scripts/roadmap-v15-bounded-pidfd.py",ROOT/"scripts/roadmap-v15-bounded-observe.py"]
    inputs += [p for p in (ROOT/"lake-manifest.json",) if p.exists()]
    helpers=("HashContainsFixture.lean","ExportEvm.lean") if phase=="fixtures" else (("ExportAll.lean",) if phase=="api" else (("CanonicalEvm.lean",) if phase=="classify" else ()))
    inputs += [ROOT/"tests/h62/item6/migrate-roadmap"/name for name in helpers]
    def fingerprint():
        return {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs}
    before=fingerprint()
    if version=="old":
        for p in inputs:
            if "tests/h62/item6/migrate-roadmap" in str(p):continue
            original=subprocess.check_output(["git","show",mod.BASE+":"+str(p.relative_to(ROOT))],cwd=ROOT)
            assert hashlib.sha256(original).hexdigest()==before[str(p.relative_to(ROOT))], "old baseline input differs from pinned base: "+str(p)
    targets=mod.graph(ROOT).closure(["Solidity.KeySort"]) if phase=="prerequisite" else (mod.graph(ROOT).closure(["Solidity.Roadmap.Evm"]) if phase in ("fixtures","classify") else c["closure"])
    toolchain=Path("/workspace/.setup/tools/lean-4.24.0-linux") if version=="old" else Path("/workspace/migrate-roadmap-toolchains/lean-4.35.0-linux")
    if version=="new":
        pin=json.loads(Path("/workspace/h62-coordinator-inputs/toolchain-pin.json").read_text())
        archive=toolchain.parent/pin["asset"]
        assert hashlib.file_digest(archive.open("rb"),"sha256").hexdigest()==pin["sha256"]
    assert (toolchain/"bin/lean").is_file()
    reused_build=None
    if phase=="api":
        reference=Path(sys.argv[3]).resolve()
        assert reference.is_relative_to(EVIDENCE) and reference.name=="result.json"
        prior=json.loads(reference.read_text())
        assert prior["exit"]==0 and prior["guard"] is None and prior["modules"]==c["closure"]
        assert all(before[k]==v for k,v in prior["inputs_after"].items())
        assert ("-"+version+"-") in prior["container"]
        reused_build=reference.parent/"build"
        assert reused_build.is_dir()
        targets=[]
    name="h62-roadmap-"+version+"-"+phase+"-"+str(time.time_ns())
    dest=(EVIDENCE/"h70"/name) if phase=="classify" else EVIDENCE/name;dest.mkdir(parents=True)
    config=dest/"runtime.toml"
    text=(ROOT/"lakefile.toml").read_text().replace("enableArtifactCache = true","enableArtifactCache = false")
    text=text.replace('version = "0.1.0"','version = "0.1.0"\nbuildDir = "'+str(reused_build or dest/"build")+'"',1)
    text=text.replace('weakLeanArgs = ["--tstack=131072"]','weakLeanArgs = ["--tstack=131072", "-j1"]')
    config.write_text(text)
    shell='set -eu; export PATH=/opt/lean/bin:$PATH; '
    shell+='test "$(cat /sys/fs/cgroup/memory.max)" = 11811160064; test "$(cat /sys/fs/cgroup/memory.swap.max)" = 0; '
    ready=dest/"limits-ready"
    release=dest/"admitted"
    shell+='touch '+shlex.quote(str(ready))+'; while ! test -f '+shlex.quote(str(release))+'; do sleep 0.05; done; '
    shell+='lean -j1 --version; lake --version; '
    shell+="trap 'echo CGROUP_PEAK; cat /sys/fs/cgroup/memory.peak' EXIT; "
    if phase=="matrix":
        status_dir=dest/"status"
        status_dir.mkdir()
        shell+='failed=0; '
        for module in targets:
            dependencies=[d for d in g.imports(module) if d in targets]
            checks=' && '.join('test -f '+shlex.quote(str(status_dir/(d+".pass"))) for d in dependencies) or 'true'
            shell+='if '+checks+'; then echo MODULE '+shlex.quote(module)+'; '
            shell+='if timeout --kill-after=5s 300s lake -f '+shlex.quote(str(config))+' --no-cache build '+shlex.quote(module)+'; then '
            shell+='touch '+shlex.quote(str(status_dir/(module+".pass")))+'; else failed=1; touch '+shlex.quote(str(status_dir/(module+".fail")))+'; fi; '
            shell+='else failed=1; touch '+shlex.quote(str(status_dir/(module+".blocked")))+'; fi; '
        shell+='exit "$failed"; '
    else:
        for module in targets:
            shell+='echo MODULE '+shlex.quote(module)+'; timeout --kill-after=5s 300s lake -f '+shlex.quote(str(config))+' --no-cache build '+shlex.quote(module)+'; '
    if phase=="api":
        shell+='timeout --kill-after=5s 300s lake -f '+shlex.quote(str(config))+' env lean --tstack=131072 -j1 '+shlex.quote(str(ROOT/"tests/h62/item6/migrate-roadmap/ExportAll.lean"))+'; '
    if phase in ("fixtures","classify"):
        for helper in helpers:
            shell+='timeout --kill-after=5s 300s lake -f '+shlex.quote(str(config))+' env lean --tstack=131072 -j1 '+shlex.quote(str(ROOT/"tests/h62/item6/migrate-roadmap"/helper))+'; '
    script=dest/"run.sh"
    script.write_text(shell+"\n")
    subprocess.run(["sh","-n",str(script)],check=True)
    env=os.environ.copy()
    for key in ("DOCKER_HOST","DOCKER_CONTEXT","DOCKER_TLS","DOCKER_TLS_VERIFY","DOCKER_CERT_PATH"):env.pop(key,None)
    cmd=DOCKER+["run","--name",name,"--network","none","--memory","11g","--memory-swap","11g","--cpus","1",
        "--user",str(os.getuid())+":"+str(os.getgid()),
        "--mount","type=bind,src="+str(ROOT)+",dst="+str(ROOT)+",readonly",
        "--mount","type=bind,src="+str(EVIDENCE)+",dst="+str(EVIDENCE),
        "--mount","type=bind,src="+str(toolchain)+",dst=/opt/lean,readonly",
        "-w",str(ROOT),"-e","LEAN_NUM_THREADS=1","-e","LEAN_SYSROOT=/opt/lean",IMAGE,"sh",str(script)]
    spec=importlib.util.spec_from_file_location("terminal_tracker",ROOT/"scripts/roadmap-v15-bounded-pidfd.py")
    terminal=importlib.util.module_from_spec(spec);spec.loader.exec_module(terminal)
    def journal(event):
        with (dest/"process-events.jsonl").open("a") as f:f.write(json.dumps(event)+"\n")
    def launch(pid):
        identity=terminal.proc_identity(pid)
        identity["argv"]=[x.decode() for x in (Path("/proc")/str(pid)/"cmdline").read_bytes().split(b"\0") if x]
        actual=os.stat(Path("/proc")/str(pid)/"exe")
        expected=os.stat(toolchain/"bin/lean")
        if (actual.st_dev,actual.st_ino)!=(expected.st_dev,expected.st_ino):
            raise terminal.GuardError("Lean executable inode differs from official selected binary")
        identity["exe"]=str((toolchain/"bin/lean").resolve())
        return identity
    tracker=terminal.TerminalTracker(journal,exe=toolchain/"bin/lean",launch=launch)
    started=time.monotonic();reason=None;peak_rss=0;samples=0;admitted=False
    with (dest/"build.log").open("w") as log:
        process=subprocess.Popen(cmd,env=env,stdout=log,stderr=subprocess.STDOUT)
        while process.poll() is None:
            if not admitted and time.monotonic()-started>15:
                reason="startup admission deadline"
                bounded_control(DOCKER+["kill",name],env=env,stdout=log,stderr=log);break
            limit=int(Path("/sys/fs/cgroup/memory.max").read_text())
            used=int(Path("/sys/fs/cgroup/memory.current").read_text())
            available=int(next(l.split()[1] for l in Path("/proc/meminfo").read_text().splitlines() if l.startswith("MemAvailable:")))*1024
            if min(limit-used,available)<4*1024**3:
                reason="4GiB reserve violated"
                bounded_control(DOCKER+["kill",name],env=env,stdout=log,stderr=log)
                break
            top=bounded_control(DOCKER+["top",name,"-eo","pid,etimes,rss,stat,comm,args"],timeout=min(2,max(0.01,15-(time.monotonic()-started))) if not admitted else 2,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.DEVNULL)
            if top.returncode==0:
                try:
                    normalized=tracker.snapshot(top.stdout)
                    rows=[r.split(None,5) for r in normalized.splitlines()[1:]]
                    peak_rss=max(peak_rss,sum(int(r[2])*1024 for r in rows));samples+=1
                    lean=[r for r in rows if r[4]=="lean" and not r[3].startswith("Z")]
                    if not admitted:
                        if time.monotonic()-started>15:raise terminal.GuardError("startup admission deadline")
                        if lean:raise terminal.GuardError("Lean ran before startup admission")
                        if ready.exists():
                            release.touch();admitted=True
                            journal(dict(event="startup-admitted",limits_verified=True))
                    if len(lean)>1 or any("-j1" not in r[5].split() for r in lean):
                        raise terminal.GuardError("serial Lean/-j1 guard violated")
                except Exception as exc:
                    (dest/"rejected-top.txt").write_text(top.stdout)
                    reason="process observation rejected: "+str(exc)
                    bounded_control(DOCKER+["kill",name],env=env,stdout=log,stderr=log);break
            else:
                state=bounded_control(DOCKER+["inspect","--format","{{.State.Status}}",name],env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.DEVNULL)
                status=state.stdout.strip()
                if (admitted and status not in ("exited","dead")) or (time.monotonic()-started>15 and status not in ("exited","dead")):
                    reason="process observation unavailable"
                    bounded_control(DOCKER+["kill",name],env=env,stdout=log,stderr=log);break
            time.sleep(0.02)
        try:code=process.wait(timeout=5)
        except subprocess.TimeoutExpired:
            reason=(reason or "Docker client stalled")+"; container termination not confirmed"
            bounded_control(DOCKER+["kill",name],env=env,stdout=log,stderr=log)
            process.kill();code=process.wait(timeout=5)
    tracker.close()
    if not admitted and code==0:reason="startup was never admitted"
    if samples==0 and code==0:reason="no process observations"
    after=fingerprint()
    if before!=after:reason="build inputs changed during run"
    result=dict(command=cmd,exit=code,guard=reason,startup_admitted=admitted,wall_seconds=time.monotonic()-started,
                sampled_peak_aggregate_rss_bytes=peak_rss,samples=samples,modules=targets,
                source_hashes={m["path"]:m["sha256"] for m in c["modules"]},
                inputs_before=before,inputs_after=after,
                tooling_sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (Path(__file__),Path(__file__).with_name("census.py"))},
                config_sha256=hashlib.sha256(config.read_bytes()).hexdigest(),script_sha256=hashlib.sha256(script.read_bytes()).hexdigest(),
                resources=dict(memory_bytes=11811160064,swap_bytes=0,cpus=1,reserve_bytes=4294967296,module_wall_limit_seconds=300,observation_sleep_seconds=0.02),
                module_statuses={m:next((status for status in ("pass","fail","blocked") if (dest/"status"/(m+"."+status)).exists()),"pending") for m in targets} if phase=="matrix" else None,
                head=subprocess.check_output(["git","rev-parse","HEAD"],cwd=ROOT,text=True).strip(),
                clean_output_initially_absent=reused_build is None,reused_build=str(reused_build) if reused_build else None,artifact_cache=False,container=name)
    (dest/"result.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(dict(evidence=str(dest),exit=code,guard=reason,wall_seconds=result["wall_seconds"])))
    return code or (1 if reason else 0)
if __name__=="__main__":sys.exit(main())
