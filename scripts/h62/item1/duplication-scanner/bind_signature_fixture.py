#!/usr/bin/env python3
"""Guard stale-olean reuse and fabricated snapshot-to-signature promotion.

Only this live canonical fixture rebuild creates local source/artifact linkage.
Raw signatures stay environment_binding=unbound. This is not remote attestation,
ABA-proof provenance, a compiler proof, or binding for other repository files.
"""
import argparse
from contextlib import contextmanager
import fcntl
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import resource
import signal
import stat
import subprocess
import sys
import time
import types

ROOT=Path(__file__).resolve().parents[4]
FIXTURES=ROOT/"tests/h62/item1/duplication-scanner"
PINS=FIXTURES/"local-rebuild-pins.json"
SOURCES={"SignatureFingerprint":["Lean"],"SignatureEnvironment":["SignatureFingerprint"],
         "SignatureEnvironmentProbe":["SignatureEnvironment"],"SignatureObservedConsumer":["SignatureEnvironment"]}


def module_from(path,name):
    module=types.ModuleType(name);module.__file__=str(path)
    exec(compile(path.read_bytes(),str(path),"exec"),module.__dict__)
    return module


observer=module_from(Path(__file__).with_name("observe_signature_environment.py"),"binding_observer")
scanner=module_from(Path(__file__).with_name("scan.py"),"binding_scanner")
bounded=module_from(ROOT/"scripts/h62/item2/audit-readonly-calls/bounded.py","binding_resource_monitor")


def sha(path):
    with path.open("rb") as f:return hashlib.file_digest(f,"sha256").hexdigest()


def regular(path):
    if not stat.S_ISREG(path.lstat().st_mode):raise ValueError("nonregular or symlink binding input: "+str(path))
    return observer.regular_hash(path)


def check_inputs(pins):
    compiler=Path(pins["lean_path"])
    if regular(compiler)["sha256"]!=pins["lean_sha256"]:raise ValueError("compiler binary substitution")
    if sha(ROOT/"lean-toolchain")!=pins["lean_toolchain_sha256"]:raise ValueError("toolchain pin drift")
    for name,digest in pins["fixture_sources"].items():
        if Path(name).name!=name or regular(FIXTURES/name)["sha256"]!=digest:
            raise ValueError("fixture source pin drift: "+name)
    for name,imports in SOURCES.items():
        text=scanner.hide_strings(scanner.mask((FIXTURES/(name+".lean")).read_text()))
        actual=[token for line in re.findall(r"(?m)^import[ \t]+([^\n]+)$",text) for token in line.split()]
        if actual!=imports:raise ValueError("noncanonical or forbidden transitive fixture import: "+name)
    return compiler


def guard():
    cg=Path("/sys/fs/cgroup")
    maximum=int((cg/"memory.max").read_text());current=int((cg/"memory.current").read_text())
    available=int(re.search(r"MemAvailable:\s+(\d+)",Path("/proc/meminfo").read_text())[1])*1024
    swap=int((cg/"memory.swap.current").read_text())
    total_swap=int(re.search(r"SwapTotal:\s+(\d+)",Path("/proc/meminfo").read_text())[1])*1024
    if swap or (total_swap and (cg/"memory.swap.max").read_text().strip()!="0") or min(maximum-current,available)<=4*1024**3:
        raise ValueError("resource reserve/no-swap guard")
    return {"memory_max":maximum,"memory_current":current,"host_available":available,"swap_current":swap}


def checked_process(command,env,log,steps,timeout=120):
    controls=guard()
    cap=min(bounded.CAP,min(controls["memory_max"]-controls["memory_current"],controls["host_available"])-bounded.RESERVE)
    def limits():resource.setrlimit(resource.RLIMIT_AS,(cap,cap))
    start=time.monotonic();reason=None;peak=0
    with log.open("xb") as stream:
        process=subprocess.Popen(command,env=env,stdin=subprocess.DEVNULL,stdout=stream,stderr=subprocess.STDOUT,
                                 start_new_session=True,preexec_fn=limits)
        try:
            while process.poll() is None:
                members=bounded.processes(process.pid)
                rss=sum(row[2] for row in members);peak=max(peak,rss)
                state=guard()
                if rss>cap:reason="aggregate memory cap"
                if sum(exe=="lean" for _,exe,_ in members)>1:reason="multiple Lean processes"
                if time.monotonic()-start>timeout:reason="wall timeout"
                if reason:break
                time.sleep(0.05)
            if not reason and any(rss>0 for _,_,rss in bounded.processes(process.pid)):
                reason="owned descendants remain after command exit"
        except BaseException as exc:
            reason="monitor stopped: "+str(exc)
        finally:
            if reason or process.poll() is None:
                try:os.killpg(process.pid,signal.SIGKILL)
                except ProcessLookupError:pass
            process.wait()
            while any(rss>0 for _,_,rss in bounded.processes(process.pid)):
                reason=reason or "waiting for owned descendants to drain"
                try:os.killpg(process.pid,signal.SIGKILL)
                except ProcessLookupError:pass
                time.sleep(0.05)
    step={"command":command,"exit":process.returncode,"timed_out":reason=="wall timeout",
          "stop_reason":reason,"seconds":time.monotonic()-start,"address_space_cap_bytes":cap,
          "log":str(log),"log_sha256":sha(log),"resources":controls,
          "peak_aggregate_rss_bytes":peak,"live_owned_descendants":0}
    steps.append(step)
    if reason or process.returncode:raise ValueError("fresh process failed or timed out: "+log.name)


def expected_log_hash(steps, path):
    """Use exactly one successful in-memory step as the log's byte authority."""
    if not isinstance(steps,list) or any(not isinstance(row,dict) for row in steps):
        raise ValueError("malformed completed log steps")
    rows=[row for row in steps if row.get("log")==str(path)]
    if len(rows)!=1:
        raise ValueError("missing or ambiguous completed log step")
    row=rows[0]
    if type(row.get("exit")) is not int or row["exit"]!=0 or row.get("timed_out") is not False or row.get("stop_reason","missing") is not None:
        raise ValueError("log step did not complete successfully")
    digest=row.get("log_sha256")
    if not isinstance(digest,str) or not re.fullmatch(r"[0-9a-f]{64}",digest):
        raise ValueError("malformed completed log hash")
    return digest


def verify_process_logs(steps):
    """Guard persistent log replacement after parsing, including child logs."""
    if not isinstance(steps,list) or any(not isinstance(row,dict) or not isinstance(row.get("log"),str) for row in steps):
        raise ValueError("malformed completed log steps")
    for row in steps:
        path=Path(row["log"]);expected=expected_log_hash(steps,path)
        if regular(path)["sha256"]!=expected:
            raise ValueError("checked process log changed after execution")


def fresh_output(path):
    try:path.lstat()
    except FileNotFoundError:return
    raise ValueError("stale or prepopulated build output: "+str(path))


def compile_module(compiler,source,output,env,logs,steps,label):
    target=output/(source.stem+".olean");fresh_output(target)
    checked_process([str(compiler),"-j1","--tstack=131072","--root="+str(source.parent),"-o",str(target),str(source)],env,logs/(label+".log"),steps)
    if regular(target)["size"]==0:raise ValueError("empty fresh compiler output")


def snapshot(log, expected_sha256=None):
    env,signatures,_=observer.read_log(log,expected_sha256)
    if signatures:raise ValueError("probe unexpectedly contains signatures")
    return observer.capture_environment(env)


def standard_closure(value,toolchain):
    result=[]
    for item in value["artifacts"]:
        name=observer.name_parts(item["module"])
        if name in [("SignatureFingerprint",),("SignatureEnvironment",)]:continue
        if name[0] not in ("Init","Lean","Std") or not Path(item["base"]["realpath"]).is_relative_to(toolchain/"lib/lean"):
            raise ValueError("forbidden external/stopped-workload dependency")
        result.append(item)
    if not result:raise ValueError("empty bundled dependency closure")
    return result


def companion_artifacts(artifacts):
    """Guard dependency IR/native companion drift, including newly appearing files."""
    result=[]
    for item in artifacts:
        base=Path(item["base"]["path"])
        stem=Path(str(base).removesuffix(".olean"))
        for suffix in (".ir",".ilean",".so"):
            path=Path(str(stem)+suffix)
            try:path.lstat()
            except FileNotFoundError:result.append({"path":str(path),"present":False});continue
            result.append({"present":True,**regular(path)})
    return result


def runtime_files(compiler):
    toolchain=compiler.parent.parent
    paths={p.resolve() for p in (toolchain/"lib").glob("*.so*") if p.is_file()}
    output=subprocess.check_output(["/usr/bin/ldd",str(compiler)],text=True,env=clean_environment(compiler))
    for line in output.splitlines():
        if "not found" in line:raise ValueError("unresolved compiler runtime")
        for token in line.split():
            if token.startswith("/"):paths.add(Path(token).resolve(strict=True))
    return [regular(p) for p in sorted(paths)]


def clean_environment(compiler):
    env={k:v for k,v in os.environ.items() if not k.startswith("LEAN_") and k not in ("LD_PRELOAD","LD_LIBRARY_PATH")}
    env.update(LEAN_NUM_THREADS="1",PATH=str(compiler.parent)+":/usr/bin:/bin",LC_ALL="C.UTF-8")
    return env


@contextmanager
def writer_lease():
    path=Path("/tmp/solidity-lean-feature-groups-20261025/writer.lock")
    path.parent.mkdir(parents=True,exist_ok=True)
    with path.open("a") as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        yield


def rebuild(output):
    """Rebuild under the caller-held writer lease; main acquires it."""
    pins=json.loads(PINS.read_text());compiler=check_inputs(pins);toolchain=compiler.parent.parent
    if not output.is_absolute():raise ValueError("binding output must be absolute")
    output.mkdir(mode=0o700,exist_ok=False)
    steps=[];receipt={"schema":1,"kind":"trusted-local-fixture-rebuild","status":"failed","steps":steps,
                      "raw_environment_binding":"unbound","compiler_sha256":pins["lean_sha256"],"pins_sha256":sha(PINS),
                      "driver_sha256":sha(Path(__file__)),
                      "observer_sha256":sha(Path(__file__).with_name("observe_signature_environment.py")),
                      "scanner_sha256":sha(Path(__file__).with_name("scan.py")),
                      "resource_monitor_sha256":sha(ROOT/"scripts/h62/item2/audit-readonly-calls/bounded.py")}
    try:
        source=output/"sources";source.mkdir(mode=0o700)
        logs=output/"logs";logs.mkdir(mode=0o700)
        for name in pins["fixture_sources"]:
            (source/name).write_bytes((FIXTURES/name).read_bytes());(source/name).chmod(0o444)
        source_manifest={name:regular(source/name) for name in pins["fixture_sources"]}
        if any(source_manifest[name]["sha256"]!=expected for name,expected in pins["fixture_sources"].items()):
            raise ValueError("staged source does not match expected pin")
        runtime=runtime_files(compiler)
        base_env=clean_environment(compiler)
        phases={}
        for phase in ("discovery","compiled"):
            dest=output/phase;dest.mkdir(mode=0o700)
            env=dict(base_env,LEAN_PATH=str(dest))
            for name in ("SignatureFingerprint","SignatureEnvironment"):
                compile_module(compiler,source/(name+".lean"),dest,env,logs,steps,phase+"-"+name)
            probe=logs/(phase+"-probe.log")
            checked_process([str(compiler),"-j1","--tstack=131072","--root="+str(source),str(source/"SignatureEnvironmentProbe.lean")],env,probe,steps)
            phases[phase]=snapshot(probe,expected_log_hash(steps,probe))
            closure=standard_closure(phases[phase],toolchain)
            if phase=="discovery":
                before_closure=closure
                before_companions=companion_artifacts(closure)
                for item in before_closure:
                    for key in ("base","server","private"):
                        entry=item[key]
                        if key=="base" or entry["present"]:regular(Path(entry["path"]))
            elif observer.canonical(closure)!=observer.canonical(before_closure):
                raise ValueError("bundled dependency changed across canonical rebuild")
        consumer=logs/"consumer.log"
        checked_process([str(compiler),"-j1","--tstack=131072","--root="+str(source),str(source/"SignatureObservedConsumer.lean")],env,consumer,steps)
        observed,lines,_=observer.read_log(consumer,expected_log_hash(steps,consumer))
        checker=module_from(source/"check_signature_records.py","bound_record_checker")
        records=checker.validate("\n".join(lines))
        after=observer.capture_environment(phases["compiled"]["environment"])
        observer.verify_observation(phases["compiled"],observed,after)
        if source_manifest!={name:regular(source/name) for name in pins["fixture_sources"]} or runtime!=runtime_files(compiler):
            raise ValueError("staged source/runtime changed during execution")
        if before_companions!=companion_artifacts(standard_closure(after,toolchain)):
            raise ValueError("bundled dependency companion changed during execution")
        check_inputs(pins)
        verify_process_logs(steps)
        receipt.update(status="pass",sources=source_manifest,bundled_dependencies=before_closure,
                       runtime=runtime,bundled_companions=before_companions,compiled_artifacts=after["artifacts"],records=records,
                       source_bindings=[{"source_path":"tests/h62/item1/duplication-scanner/SignatureFingerprint.lean",
                                         "source_sha256":pins["fixture_sources"]["SignatureFingerprint.lean"],
                                         "declaration":r["declaration"],"signature":r["signature"]} for r in records],
                       boundary="Fresh canonical execution binds only these five fixture records to copied pinned sources, fresh local oleans and observed bundled dependencies. Trusted executor/compiler and absence of concurrent unauthorized mutation are operational limits, not theorem premises. Pre/post hashes do not eliminate ABA; this is not remote attestation or general Solidity signature binding.")
    except Exception as exc:
        receipt["error"]=str(exc)
        raise
    finally:
        (output/"receipt.json").write_text(json.dumps(receipt,indent=2)+"\n")
    return receipt


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument("--output",type=Path,required=True);a=p.parse_args()
    try:
        with writer_lease():result=rebuild(a.output)
    except (OSError,ValueError,subprocess.SubprocessError) as exc:
        p.exit(1,"LOCAL_REBUILD_REJECT: "+str(exc)+"\n")
    print("LOCAL_FIXTURE_REBUILD_PASS records="+str(len(result["records"]))+" raw_environment_binding=unbound; no global binding/attestation claim")


if __name__=="__main__":main()
