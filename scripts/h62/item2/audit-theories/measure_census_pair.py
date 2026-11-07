#!/usr/bin/env python3
"""One authorized matched census timing pair: same input, machine, cache and bounds.
Changes only optional audit-tool serialization (.pretty to .compress). All decoded
JSON records/string fields must match the original and the before result exactly.
Keeps the original evidence/cache immutable; no additional timing retries.
"""
import argparse, hashlib, json, os, resource, shutil, signal, subprocess, time
from pathlib import Path
import fcntl
import verify_census as verification
from census import ROOT
from serial_check import available, limits, GIB

SOURCE="tests/h62/item2/audit-theories/ElaboratedCensus.lean"

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()

def census_sources(original):
    baseline=original.replace("run_cmd do\n","run_cmd do\n  let auditStarted ← liftIO IO.monoNanosNow\n",1)
    baseline=baseline.replace("  let some path ←", "  let auditExtracted ← liftIO IO.monoNanosNow\n  let some path ←",1)
    old='  liftIO <| IO.FS.writeFile path ((Json.arr rows).pretty ++ "\\n")'
    new='  let auditPayload := (Json.arr rows).pretty ++ "\\n"\n  let auditRendered ← liftIO IO.monoNanosNow\n  liftIO <| IO.FS.writeFile path auditPayload\n  let auditWritten ← liftIO IO.monoNanosNow\n  logInfo m!"H62_CENSUS_STAGES extraction_ns={auditExtracted - auditStarted} serialization_ns={auditRendered - auditExtracted} write_ns={auditWritten - auditRendered}"'
    assert baseline.count(old)==1
    baseline=baseline.replace(old,new)
    optimized=baseline.replace('(Json.arr rows).pretty ++', '(Json.arr rows).compress ++')
    assert optimized!=baseline
    return baseline,optimized

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--lean",type=Path,required=True)
    ap.add_argument("--seed",type=Path,required=True,help="Previously checked evidence directory")
    ap.add_argument("--out",type=Path,required=True)
    ap.add_argument("--baseline-ref",default="304bda598101b57459d717022181352128c5d02b",help="Committed unoptimized census source")
    a=ap.parse_args(); lean=a.lean.resolve(); seed=a.seed.resolve(); out=a.out.resolve()
    if out.is_relative_to(ROOT) or out.exists(): raise SystemExit("Use a NEW absolute off-Git evidence directory")
    if not a.out.is_absolute(): raise SystemExit("Output must be absolute")
    lock=Path("/tmp/solidity-lean-feature-groups-20261025/writer.lock")
    lock.parent.mkdir(parents=True,exist_ok=True)
    with lock.open("a") as lk:
        fcntl.flock(lk,fcntl.LOCK_EX)
        status=subprocess.check_output(["git","status","--short","--branch"],cwd=ROOT,text=True)
        print(status,flush=True)
        entry_source=(ROOT/SOURCE).read_text()
        committed=subprocess.check_output(["git","show","HEAD:"+SOURCE],cwd=ROOT,text=True)
        if entry_source!=committed: raise SystemExit("Unexpected census source changes; preserve before retrying")
        original=subprocess.check_output(["git","show",a.baseline_ref+":"+SOURCE],cwd=ROOT,text=True)
        baseline,optimized=census_sources(original)
        if entry_source not in (original,optimized):
            raise SystemExit("Current source differs from the selected baseline/optimization; preserve it")
        version=subprocess.check_output([str(lean),"--version"],text=True).strip()
        lake_version=subprocess.check_output([str(lean.with_name("lake")),"--version"],text=True).strip()
        verification.VERSION=version
        verification.FINGERPRINTS.clear()
        key_meta,_=verification.checked_module(seed/"serial","Solidity/KeySort.lean")
        verification.checked_module(seed/"serial",SOURCE,source_text=original)
        assert json.loads((seed/"serial/baseline-results.json").read_text())["version"]==version
        swap=next(l for l in Path("/proc/meminfo").read_text().splitlines() if l.startswith("SwapTotal:"))
        if int(swap.split()[1]): raise SystemExit("No-swap prerequisite failed")
        if available()<4*GIB: raise SystemExit("4GiB available reserve prerequisite failed")
        out.mkdir(parents=True)
        serial=out/"serial";serial.mkdir()
        shutil.copytree(seed/"serial/olean",serial/"olean")
        shutil.copy2(seed/"serial/baseline-results.json",serial/"baseline-results.json")
        shutil.copytree(seed/"census",out/"census")
        lib=serial/"olean"
        (out/"original.lean").write_text(original)
        env=os.environ.copy();env["LEAN_NUM_THREADS"]="1";env["LEAN_PATH"]=str(lib)
        shared=out/"matched-input-output.json"
        shutil.copy2(seed/"elaborated.json",shared)
        env["H62_AUDIT_CENSUS_OUT"]=str(shared)
        warm_paths=sorted(lib.rglob("*.olean"))+sorted((lean.parent.parent/"lib/lean").rglob("*.olean"))
        warm_digest=hashlib.sha256()
        for path in warm_paths: warm_digest.update(str(path).encode()+b"\0")
        warm_manifest=warm_digest.hexdigest()
        def warm():
            for path in warm_paths:
                with path.open("rb") as f:
                    for _ in iter(lambda:f.read(1024*1024),b""): pass
        def cpu_stat():
            return {k:int(v) for k,v in (line.split() for line in Path("/sys/fs/cgroup/cpu.stat").read_text().splitlines())}
        def execute(label,source,output):
            if available()<4*GIB: raise RuntimeError("4GiB reserve failed before "+label)
            log=out/(label+".log")
            command=[str(lean),"-j1","--tstack=131072","-o",str(output),source]
            before_cpu=resource.getrusage(resource.RUSAGE_CHILDREN);cg_before=cpu_stat()
            started=time.monotonic();peak=0;reason=None
            with log.open("w") as stream:
                process=subprocess.Popen(command,cwd=ROOT,env=env,stdout=stream,stderr=subprocess.STDOUT,
                    start_new_session=True,preexec_fn=limits)
                try:
                    while process.poll() is None:
                        try:
                            rss=next(l for l in Path(f"/proc/{process.pid}/status").read_text().splitlines() if l.startswith("VmRSS:"))
                            peak=max(peak,int(rss.split()[1])*1024)
                        except (FileNotFoundError,StopIteration): pass
                        if available()<4*GIB: reason="available reserve below4GiB"
                        if time.monotonic()-started>300:reason="300s module budget"
                        if reason:
                            os.killpg(process.pid,signal.SIGTERM)
                            try: process.wait(timeout=5)
                            except subprocess.TimeoutExpired: os.killpg(process.pid,signal.SIGKILL);process.wait()
                            break
                        time.sleep(.1)
                finally:
                    if process.poll() is None:
                        os.killpg(process.pid,signal.SIGKILL);process.wait()
            elapsed=time.monotonic()-started
            after_cpu=resource.getrusage(resource.RUSAGE_CHILDREN);cg_after=cpu_stat()
            verification.FINGERPRINTS.clear()
            record={"label":label,"command":command,"exit":process.returncode,"seconds":round(elapsed,6),
                "user_seconds":after_cpu.ru_utime-before_cpu.ru_utime,"system_seconds":after_cpu.ru_stime-before_cpu.ru_stime,
                "peak_rss_bytes":peak,"resource_stop":reason,"log":str(log),
                "source_sha256":sha(ROOT/source),"source_transitive_sha256":verification.fingerprint(source),
                "cpu_stat_delta":{k:cg_after[k]-v for k,v in cg_before.items()},"load_average":os.getloadavg()}
            if process.returncode==0 and not reason:
                record["olean_sha256"]=sha(output);record["log_sha256"]=sha(log)
                output.with_suffix(".audit-result.json").write_text(json.dumps(record,indent=2)+"\n")
                output.with_suffix(".audit-hash").write_text(record["source_transitive_sha256"])
            (out/(label+"-result.json")).write_text(json.dumps(record,indent=2)+"\n")
            print(json.dumps(record),flush=True)
            if process.returncode or reason: raise RuntimeError("Matched check failed: "+label)
            return record
        # Fresh prerequisite is not an additional census timing trial.
        key=execute("keysort","Solidity/KeySort.lean",lib/"Solidity/KeySort.olean")
        (out/"before.lean").write_text(baseline);(out/"after.lean").write_text(optimized)
        target=lib/Path(SOURCE).with_suffix(".olean")
        try:
            (ROOT/SOURCE).write_text(baseline)
            warm()
            before=execute("before",SOURCE,target)
            shutil.copy2(shared,out/"before.json")
            shutil.copy2(target,out/"before.olean")
            # Warm the same cache paths again, including the census output.
            # It is never imported; its before/after hashes are recorded separately.
            (ROOT/SOURCE).write_text(optimized)
            warm()
            after=execute("after",SOURCE,target)
            shutil.copy2(shared,out/"after.json")
            before_json=json.loads((out/"before.json").read_bytes())
            after_json=json.loads((out/"after.json").read_bytes())
            original_json=json.loads((seed/"elaborated.json").read_bytes())
            assert before_json==after_json==original_json,"Census semantic output changed"
            delta=(after["seconds"]/before["seconds"]-1)*100
            result={"status":"pass" if delta<=10 else "fail","before":before,"after":after,
                "delta_percent":delta,"threshold_percent":10,"same_decoded_input_and_output":True,
                "records":len(after_json),"same_machine":True,"same_command":before["command"]==after["command"],
                "same_output_destination":str(shared),"same_environment":{"LEAN_NUM_THREADS":"1","LEAN_PATH":str(lib)},
                "warm_input_path_manifest_sha256":warm_manifest,"warm_input_files":len(warm_paths),
                "versions":{"lean":version,"lake":lake_version},"keysort":key,
                "bounds":{"address_space_gib":12,"available_reserve_gib":4,"module_timeout_seconds":300,"swap_total_kib":0},
                "before_bytes":(out/"before.json").stat().st_size,"after_bytes":(out/"after.json").stat().st_size,
                "cause_evidence":"See identical-input stage timings and CPU/throttling deltas; no retry or additional timing pair."}
            (out/"matched-pair.json").write_text(json.dumps(result,indent=2)+"\n")
            print("MATCHED_PAIR_"+result["status"].upper()+" "+json.dumps({"before_seconds":before["seconds"],"after_seconds":after["seconds"],"delta_percent":delta,"records":len(after_json)}),flush=True)
        except BaseException:
            (ROOT/SOURCE).write_text(entry_source)
            raise

if __name__=="__main__":main()
