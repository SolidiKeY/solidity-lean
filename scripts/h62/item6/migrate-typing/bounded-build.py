#!/usr/bin/env python3
"""Serial clean source build, independent of Lake/master artifact caches.

No timing comparison is valid unless both result files passed with identical
settings and identical source hashes. Final repository gate is still required.
"""
import argparse, fcntl, hashlib, importlib.util, json, os, pathlib, resource, signal, subprocess, time

GIB=1024**3
SPEC=importlib.util.spec_from_file_location("census",pathlib.Path(__file__).with_name("census.py"))
census=importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(census)

def run():
    ap=argparse.ArgumentParser(); ap.add_argument("--lean",type=pathlib.Path,required=True); ap.add_argument("--output",type=pathlib.Path,required=True); ap.add_argument("--root",type=pathlib.Path,default=pathlib.Path.cwd()); ap.add_argument("--only-keysort",action="store_true"); ap.add_argument("--expect-base-sources",action="store_true"); ap.add_argument("--fixture",type=pathlib.Path); ap.add_argument("--imports",type=pathlib.Path)
    a=ap.parse_args(); root=a.root.resolve(); out=a.output.resolve(); lean=a.lean.resolve()
    lock=pathlib.Path("/tmp/solidity-lean-feature-groups-20261025/writer.lock").open("a")
    fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    subprocess.run(["git","status","--short"],cwd=root,check=True)
    out.mkdir(parents=True,exist_ok=False)
    if pathlib.Path("/proc/swaps").read_text().splitlines()[1:]: raise RuntimeError("swap enabled")
    settings={"lean_threads":1,"lean_memory_mib":8192,"tstack_kib":131072,"aggregate_rss_cap_gib":10,"reserve_gib":4,"address_space_cap_gib":12,"cache":"none; fresh olean-only import closure","poll_seconds":0.1}
    versions={"lean":subprocess.check_output([str(lean),"--version"],text=True).strip(),"lake":subprocess.check_output([str(lean.with_name("lake")),"--version"],text=True).strip()}
    subprocess.run(["git","merge-base","--is-ancestor",census.BASE,"HEAD"],cwd=root,check=True)
    provenance={"head":subprocess.check_output(["git","rev-parse","HEAD"],cwd=root,text=True).strip(),"branch":subprocess.check_output(["git","branch","--show-current"],cwd=root,text=True).strip(),"base":census.BASE,"cpu_affinity":sorted(os.sched_getaffinity(0)),"cpu_max":pathlib.Path("/sys/fs/cgroup/cpu.max").read_text().strip(),"memory_max":pathlib.Path("/sys/fs/cgroup/memory.max").read_text().strip(),"swap_table":pathlib.Path("/proc/swaps").read_text()}
    snapshot=census.census(root); (out/"census.json").write_text(json.dumps(snapshot,sort_keys=True,indent=2)+"\n")
    if a.fixture and (a.fixture.is_absolute() or not str(a.fixture).startswith("tests/h62/item6/migrate-typing/")):
        raise ValueError("fixture must be a scoped relative path")
    order=[str(a.fixture.with_suffix("")).replace("/", ".")] if a.fixture else (["Solidity.KeySort"] if a.only_keysort else snapshot["local_build_order"])
    env=os.environ.copy(); env["LEAN_NUM_THREADS"]="1"; env["LEAN_PATH"]=str(out/"lib")+(os.pathsep+str(a.imports.resolve()) if a.imports else "")
    closure_hashes={m:census.digest((root/(m.replace(".","/")+".lean")).read_bytes()) for m in order}
    base_hashes={} if a.fixture else {m:census.digest(subprocess.check_output(["git","show",census.BASE+":"+m.replace(".","/")+".lean"],cwd=root)) for m in order}
    provenance["all_closure_sources_equal_base"]=closure_hashes==base_hashes
    if a.expect_base_sources and closure_hashes!=base_hashes: raise RuntimeError("baseline sources differ from pinned base")
    records=[]; peak=0; started=time.monotonic(); stopped=None
    def reserve():
        mem=dict(line.split(":",1) for line in pathlib.Path("/proc/meminfo").read_text().splitlines())
        host_avail=int(mem["MemAvailable"].split()[0])*1024
        cg=pathlib.Path("/sys/fs/cgroup")
        cgmax=(cg/"memory.max").read_text().strip()
        return min(host_avail,int(cgmax)-int((cg/"memory.current").read_text()) if cgmax != "max" else host_avail)
    def terminate(p):
        try: os.killpg(p.pid,signal.SIGTERM)
        except ProcessLookupError: pass
        try: p.wait(timeout=5)
        except subprocess.TimeoutExpired:
            try: os.killpg(p.pid,signal.SIGKILL)
            except ProcessLookupError: pass
            p.wait()
        # A reaped group leader can leave descendants: terminate that owned group.
        try: os.killpg(p.pid,signal.SIGKILL)
        except ProcessLookupError: pass
    def interrupted(signum,frame): raise KeyboardInterrupt("signal "+str(signum))
    signal.signal(signal.SIGTERM,interrupted)
    def limits(): resource.setrlimit(resource.RLIMIT_AS,(12*GIB,12*GIB))
    for m in order:
        src=root/(m.replace(".","/")+".lean"); target=out/"lib"/(m.replace(".","/")+".olean"); target.parent.mkdir(parents=True,exist_ok=True)
        cmd=[str(lean),"-j1","--tstack=131072","-M8192","-o",str(target),str(src.relative_to(root))]
        module_start=time.monotonic(); module_peak=0; reason=None
        if reserve()<4*GIB:
            stopped=m; records.append({"module":m,"exit":None,"resource_stop":"PREFLIGHT_RESERVE_STOP"}); break
        with (out/(m+".log")).open("w") as log:
            p=subprocess.Popen(cmd,cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True,preexec_fn=limits)
            try:
                while p.poll() is None:
                    rss=0
                    for proc in pathlib.Path("/proc").glob("[0-9]*"):
                        try:
                            stat=(proc/"stat").read_text().rsplit(")",1)[1].split()
                            if int(stat[2])==p.pid: rss+=int(stat[21])*os.sysconf("SC_PAGE_SIZE")
                        except (OSError,ValueError,IndexError): pass
                    module_peak=max(module_peak,rss); peak=max(peak,rss)
                    if rss>10*GIB or reserve()<4*GIB:
                        reason="RESOURCE_STOP"; break
                    time.sleep(0.1)
            except BaseException as exc:
                reason="MONITOR_STOP: "+repr(exc)
            finally:
                if reason: terminate(p)
            rc=p.wait()
        records.append({"module":m,"command":cmd,"exit":rc,"wall_seconds":time.monotonic()-module_start,"peak_aggregate_rss_bytes":module_peak,"resource_stop":reason,"source_sha256":hashlib.sha256(src.read_bytes()).hexdigest()})
        print(m,rc,round(records[-1]["wall_seconds"],3),flush=True)
        if rc or reason: stopped=m; break
    after_hashes={m:census.digest((root/(m.replace(".","/")+".lean")).read_bytes()) for m in order}
    if after_hashes != closure_hashes: stopped="SOURCE_DRIFT"
    result={"fixture":str(a.fixture) if a.fixture else None,"imports":str(a.imports) if a.imports else None,"provenance":provenance,"closure_source_sha256":closure_hashes,"source_drift":after_hashes != closure_hashes,"versions":versions,"settings":settings,"records":records,"passed":not stopped,"failed_module":stopped,"wall_seconds":time.monotonic()-started,"peak_aggregate_rss_bytes":peak,"children_maxrss_kib":resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,"planned_modules":len(order)}
    (out/"result.json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    raise SystemExit(0 if result["passed"] else 1)

if __name__=="__main__": run()
