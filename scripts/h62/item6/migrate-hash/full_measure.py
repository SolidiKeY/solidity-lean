#!/usr/bin/env python3
"""Serial, clean full repository gate from the pinned base, in a private worktree.
No dependency-owner sources are edited. Each module's imported predecessors are
built first, so a Lake action cannot start concurrent missing Lean dependencies.
The unchanged run-lean.sh then validates all default targets and TestSuite.
Per-module growth is reported, never used as a migration stop decision.
"""
import argparse, hashlib, json, os, pathlib, re, resource, signal, subprocess, time
from lean_lex import strip_comments
ap=argparse.ArgumentParser()
ap.add_argument("toolchain",type=pathlib.Path)
ap.add_argument("output",type=pathlib.Path)
ap.add_argument("--migrated",action="store_true")
a=ap.parse_args()
root=pathlib.Path.cwd(); out=a.output.resolve(); tool=a.toolchain.resolve()
out.mkdir(parents=True,exist_ok=False)
source=out/"source"; base="c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
subprocess.run(["git","worktree","add","--detach",str(source),base],check=True,stdout=subprocess.DEVNULL)
if a.migrated:
    for name in ("CollisionBound","Adaptive"):
        (source/f"Solidity/Hash/{name}.lean").write_bytes((root/f"Solidity/Hash/{name}.lean").read_bytes())
    (source/"lean-toolchain").write_text("leanprover/lean4:v4.35.0\n")
# Private override is identical in both arms. Production lakefile remains untouched.
config=(source/"lakefile.toml").read_text().replace("enableArtifactCache = true","enableArtifactCache = false")
config=config.replace('version = "0.1.0"','version = "0.1.0"\nmoreLeanArgs = ["-j1", "--tstack=131072"]',1)
private=source/".lake/hash-migration-full.toml"; private.parent.mkdir(exist_ok=True); private.write_text(config)
shim=out/"bin"; shim.mkdir()
import shlex
(shim/"lake").write_text("#!/bin/sh\nexec "+shlex.quote(str(tool/"bin/lake"))+" --no-cache -f "+shlex.quote(str(private))+' "$@"\n')
(shim/"lake").chmod(0o755)
env=dict(os.environ,PATH=str(shim)+":"+str(tool/"bin")+":"+os.environ["PATH"],LEAN_NUM_THREADS="1",XDG_CACHE_HOME=str(out/"cache"),SOLKEY_RULES="/workspace/.setup/solkey/keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key")
env.pop("LEAN_PATH",None)
cap=12*1024**3; reserve=4*1024**3

def available():
    mem={x.split(":")[0]:int(x.split()[1])*1024 for x in pathlib.Path("/proc/meminfo").read_text().splitlines()}
    assert mem["SwapTotal"]==0,"swap configured"
    cg=pathlib.Path("/sys/fs/cgroup"); maximum=(cg/"memory.max").read_text().strip()
    return min(mem["MemAvailable"],int(maximum)-int((cg/"memory.current").read_text())) if maximum!="max" else mem["MemAvailable"]

def limits():
    resource.setrlimit(resource.RLIMIT_AS,(cap,cap)); os.setsid()

tracked=subprocess.check_output(["git","ls-files"],cwd=source,text=True).splitlines()
hashes={p:hashlib.sha256((source/p).read_bytes()).hexdigest() for p in tracked if (source/p).is_file()}
(out/"inputs.json").write_text(json.dumps(hashes,indent=2)+"\n")
versions={x:subprocess.check_output([str(tool/"bin"/x),"--version"],text=True).strip() for x in ("lean","lake")}
(out/"settings.json").write_text(json.dumps({"base":base,"migrated":a.migrated,"toolchain":str(tool),"versions":versions,"private_config_sha256":hashlib.sha256(config.encode()).hexdigest(),"cap":cap,"reserve":reserve,"module_timeout_seconds":300,"final_gate_timeout_seconds":1800,"threads":1,"native_facets":["o","o.noexport"],"serial_executables":["solkeycheck","solidity-lean"],"cache":"fresh, disabled", "source":str(source)},indent=2)+"\n")
# Resolve registered local imports. Lean/Std/Init are official toolchain modules.
modules={p[:-5].replace("/","."):source/p for p in tracked if p.endswith(".lean") and not p.startswith(("Bridge/","tests/","vendor/"))}
for p in (source/"vendor/LeanTeX").rglob("*.lean"):
    modules[str(p.relative_to(source/"vendor/LeanTeX"))[:-5].replace("/",".")]=p
roots=["Solidity","SolidityExamples","SolkeyCheck","SolidityLean","SolkeyTestSuite"]
ordered=[]; seen=set(); visiting=set()
def visit(m):
    if m in seen or m.split(".")[0] in ("Lean","Std","Init"): return
    assert m in modules,("unresolved local import",m)
    assert m not in visiting,("import cycle",m)
    visiting.add(m)
    for line in strip_comments(modules[m].read_text()).splitlines():
        match=re.match(r"^import\s+([A-Za-z0-9_.]+)",line)
        if match: visit(match[1])
    visiting.remove(m); seen.add(m); ordered.append(m)
for m in roots: visit(m)
# Prerequisite always first; an imported predecessor will be reused afterwards.
ordered=["Solidity.KeySort"]+[m for m in ordered if m!="Solidity.KeySort"]
(out/"modules.json").write_text(json.dumps(ordered,indent=2)+"\n")
results=[]; began=time.monotonic()
for index,module in enumerate(ordered+["EXE_SOLKEYCHECK","EXE_SOLIDITYLEAN","FINAL_RUN_LEAN"]):
    assert available()>=reserve,"insufficient memory reserve"
    if module=="FINAL_RUN_LEAN": cmd=["bash","run-lean.sh"]
    elif module.startswith("EXE_"):
        cmd=[str(shim/"lake"),"build","solkeycheck" if module=="EXE_SOLKEYCHECK" else "solidity-lean"]
    else:
        cmd=["bash","-c",'"$1" build "+$2:o" && "$1" build "+$2:o.noexport"',"_",str(shim/"lake"),module]
    start=time.monotonic(); stopped=None
    with (out/(module+".log")).open("w") as log:
        child=subprocess.Popen(cmd,cwd=source,env=env,stdout=log,stderr=subprocess.STDOUT,preexec_fn=limits)
        try:
            while True:
                pid,status,usage=os.wait4(child.pid,os.WNOHANG)
                if pid: break
                if available()<reserve: stopped="MEMORY_RESERVE"
                if time.monotonic()-start>(1800 if module=="FINAL_RUN_LEAN" else 300):
                    stopped="FINAL_GATE_TIMEOUT" if module=="FINAL_RUN_LEAN" else "MODULE_TIMEOUT"
                if stopped:
                    os.killpg(child.pid,signal.SIGKILL); _,status,usage=os.wait4(child.pid,0); break
                time.sleep(0.1)
            code=os.waitstatus_to_exitcode(status); child.returncode=code
        finally:
            if child.returncode is None:
                try: os.killpg(child.pid,signal.SIGKILL)
                except ProcessLookupError: pass
                child.wait()
    row={"index":index,"module":module,"command":cmd,"exit":code,"wall_seconds":time.monotonic()-start,"max_rss_kib":usage.ru_maxrss,"resource_stop":stopped}
    results.append(row)
    (out/"results.json").write_text(json.dumps(results,indent=2)+"\n")
    print(json.dumps(row),flush=True)
    if code or stopped: break
unchanged=all(hashlib.sha256((source/p).read_bytes()).hexdigest()==h for p,h in hashes.items())
summary={"exit":results[-1]["exit"],"completed_modules":sum(r["exit"]==0 for r in results if r["module"] in ordered),"total_modules":len(ordered),"full_gate_pass":results[-1]["module"]=="FINAL_RUN_LEAN" and results[-1]["exit"]==0,"wall_seconds":time.monotonic()-began,"max_rss_kib":max(r["max_rss_kib"] for r in results),"inputs_unchanged":unchanged,"resource_stop":results[-1]["resource_stop"]}
(out/"summary.json").write_text(json.dumps(summary,indent=2)+"\n")
assert unchanged,"source inputs changed during full build"
raise SystemExit(summary["exit"] or (0 if summary["full_gate_pass"] else 1))
