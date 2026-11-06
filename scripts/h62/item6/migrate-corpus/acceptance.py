#!/usr/bin/env python3
"""Adversarial controls for audit and runner failure reporting; no Lean server."""
import importlib.util,json,os,pathlib,shutil,signal,subprocess,sys,tempfile,time
root=pathlib.Path(__file__).resolve().parents[4]; scripts=pathlib.Path(__file__).parent
spec=importlib.util.spec_from_file_location("corpus_census",scripts/"census.py"); census=importlib.util.module_from_spec(spec);spec.loader.exec_module(census)
manifest=json.loads(pathlib.Path(sys.argv[1]).read_text()); out=pathlib.Path(sys.argv[2]);out.mkdir(parents=True,exist_ok=False)
checks=[]
with tempfile.TemporaryDirectory() as temp:
    temp=pathlib.Path(temp)
    for f in manifest["files"]:
        dest=temp/f["path"];dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(root/f["path"],dest)
    assert not any(census.validate_sources(manifest,temp).values())
    f=temp/manifest["files"][0]["path"]; saved=f.read_bytes();f.write_bytes(saved+b"\n-- negative control\n")
    assert census.validate_sources(manifest,temp)["changed"];f.write_bytes(saved)
    f.unlink();assert census.validate_sources(manifest,temp)["missing"];f.write_bytes(saved)
    extra=f.parent/"Injected.lean";extra.write_text("-- unexpected case control\n")
    assert census.validate_sources(manifest,temp)["unexpected"]
    extra.unlink();nested=f.parent/"Nested"/"Injected.lean";nested.parent.mkdir();nested.write_text("-- nested injection\n")
    assert census.validate_sources(manifest,temp)["unexpected"]
checks.append("source-byte mutation, missing module, immediate/nested injected module rejected")
# A command handling TERM with exit 0 must still yield a failed wrapper stop.
child="import signal,time;signal.signal(signal.SIGTERM,lambda *_:exit(0));time.sleep(30)"
cmd=[sys.executable,str(scripts/"bounded.py"),"--out",str(out/"timeout"),"--timeout","0.5","--",sys.executable,"-c",child]
r=subprocess.run(cmd,cwd=root,capture_output=True,text=True)
record=json.loads((out/"timeout/result.json").read_text());assert r.returncode==124 and record["child_exit"]==0
checks.append("timeout remains failure when child exits 0")
# Direct termination of the wrapper must clean up its separately-sessioned child.
cmd=[sys.executable,str(scripts/"bounded.py"),"--out",str(out/"signal"),"--",sys.executable,"-c","import os,time;print(os.getpid(),flush=True);time.sleep(30)"]
p=subprocess.Popen(cmd,cwd=root,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
try:
    deadline=time.monotonic()+10
    log=out/"signal/output.log"
    while time.monotonic()<deadline:
        if log.exists() and log.read_text().strip(): break
        if p.poll() is not None: raise AssertionError(p.communicate())
        time.sleep(.05)
    leaf=int(log.read_text().strip());p.send_signal(signal.SIGTERM);p.communicate(timeout=10)
    assert p.returncode==124
    status=pathlib.Path(f"/proc/{leaf}/stat")
    assert not status.exists() or status.read_text().rsplit(")",1)[1].split()[0]=="Z"
finally:
    if p.poll() is None:p.kill();p.wait()
checks.append("external SIGTERM fails wrapper and terminates child")
# Detached descendants must be measured and reaped even if their parent exits.
leaf_code="import signal,time;signal.signal(signal.SIGTERM,signal.SIG_IGN);region=bytearray(32*1024*1024);print('ready',flush=True);time.sleep(30)"
parent_code="import subprocess,sys,time;p=subprocess.Popen([sys.executable,'-c',"+repr(leaf_code)+"],start_new_session=True,stdout=subprocess.PIPE,text=True);p.stdout.readline();print(p.pid,flush=True);time.sleep(.6)"
r=subprocess.run([sys.executable,str(scripts/"bounded.py"),"--out",str(out/"detached"),"--timeout","5","--",sys.executable,"-c",parent_code],cwd=root,capture_output=True,text=True)
leaf=int((out/"detached/output.log").read_text().strip())
try:
    assert r.returncode==0,r.stdout+r.stderr
    record=json.loads((out/"detached/result.json").read_text())
    assert record["peak_aggregate_rss_bytes"]>=32*1024*1024
    status=pathlib.Path(f"/proc/{leaf}/stat")
    assert not status.exists() or status.read_text().rsplit(")",1)[1].split()[0]=="Z"
finally:
    try:os.kill(leaf,signal.SIGKILL)
    except ProcessLookupError:pass
checks.append("detached 32 MiB descendant measured and terminated after parent success")
# Synthetic measurements exercise policy only; these are not performance data.
provenance=dict(schema="corpus-clean-v1",base="synthetic",targets=["SolidityCorpus"],clean=True,
                cache_policy="absent-output;artifact-cache-disabled;--no-cache",input_tree_sha256="0"*64,config_policy_sha256="1"*64)
base=dict(benchmark=provenance,command=["lake","build","SolidityCorpus"],per_process_as_cap_bytes=None,exit=0,resource_stop=None,wall_seconds=100,peak_aggregate_rss_bytes=100,threads=1,rss_stop_threshold_bytes=12,hard_vm_cap_bytes=16,reserve_bytes=4,swap_total_bytes=0,synthetic=True)
for label,change,expected in [("same",{},0),("exact-ten",{"wall_seconds":110},4),("missing-as",{"_drop_as_key":True},2),("slowdown",{"wall_seconds":111},3),("failed",{"exit":1},2),("nonfinite",{"wall_seconds":float("nan")},2),
("different-target",{"command":["lake","build","Other"]},2),
("different-source",{"benchmark":provenance|{"input_tree_sha256":"2"*64}},2),
("cached",{"benchmark":provenance|{"clean":False}},2),
("different-as-limit",{"per_process_as_cap_bytes":12},2)]:
    candidate=base|change
    if candidate.pop("_drop_as_key",False):candidate.pop("per_process_as_cap_bytes")
    (out/"synthetic-old.json").write_text(json.dumps(base));(out/"synthetic-new.json").write_text(json.dumps(candidate))
    r=subprocess.run([sys.executable,str(scripts/"compare.py"),str(out/"synthetic-old.json"),str(out/"synthetic-new.json")],capture_output=True,text=True)
    assert r.returncode==expected
    (out/(label+"-policy.json")).write_text(r.stdout)
checks.append("synthetic >10% slowdown stops; failed/nonfinite/incomparable/unclean runs rejected")
(out/"acceptance.json").write_text(json.dumps(dict(status="pass",checks=checks),indent=2)+"\n")
print(json.dumps(dict(status="pass",checks=checks)))
