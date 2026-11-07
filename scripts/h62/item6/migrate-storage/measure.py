#!/usr/bin/env python3
"""Clean component elaboration benchmark, never a full repository gate.
Uses an offline Docker cgroup, serial per-file Lean, and no Lake caches.
Output root must be NEW; baseline and candidate share identical controls.
"""
import argparse,fcntl,hashlib,json,os,pathlib,signal,subprocess,time
from census import ROOT,census,frozen_matches,digest
from prepare_owner_overlay import validate_postimage
D=["docker","--host=unix:///var/run/docker.sock"]
ENV={k:v for k,v in os.environ.items() if k not in ["DOCKER_HOST","DOCKER_CONTEXT","DOCKER_TLS","DOCKER_TLS_VERIFY","DOCKER_CERT_PATH"]}
LIMIT=12*1024**3;RESERVE=4*1024**3

def cmd(args,**kw):return subprocess.check_output(D+args,env=ENV,timeout=15,**kw)
def available():
 host=next(int(x.split()[1])*1024 for x in pathlib.Path("/proc/meminfo").read_text().splitlines() if x.startswith("MemAvailable:"))
 return min(host,int(pathlib.Path("/sys/fs/cgroup/memory.max").read_text())-int(pathlib.Path("/sys/fs/cgroup/memory.current").read_text()))
def no_competing_lean(cid=None):
 for p in pathlib.Path("/proc").iterdir():
  if not p.name.isdigit():continue
  try:
   if (p/"comm").read_text().strip() not in ["lean","lake"]:continue
   cg=(p/"cgroup").read_text()
  except FileNotFoundError:continue
  assert cid and cid in cg,"competing host Lean/Lake: "+p.name

def sha(path):
 h=hashlib.sha256()
 with path.open("rb") as f:
  for b in iter(lambda:f.read(1024*1024),b""):h.update(b)
 return h.hexdigest()

def interrupted(signum,frame):raise RuntimeError("controller signal "+str(signum))

def main():
 a=argparse.ArgumentParser();a.add_argument("toolchain",type=pathlib.Path);a.add_argument("output",type=pathlib.Path);a.add_argument("--image",required=True);a.add_argument("--owner-fixture",type=pathlib.Path);a.add_argument("--timeout",type=int,default=600);x=a.parse_args()
 assert x.toolchain.is_absolute() and x.output.is_absolute()
 assert not x.output.exists(),"refuse non-clean output"
 lock=open("/tmp/solidity-lean-feature-groups-20261025/writer.lock","r+");fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
 subprocess.run(["git","-C",str(ROOT),"status","--short","--branch"],check=True)
 graph=census();assert graph["closure_matches_checkout"],"external source drift";assert all(f["unchanged"] for f in graph["files"])
 source_root=ROOT;source_manifest=None;source_manifest_sha=None
 source_tree={m.replace(".","/")+".lean":h for m,h in graph["closure_source_sha256"].items()}
 compiled_hashes=graph["closure_source_sha256"]
 if x.owner_fixture:
  assert x.owner_fixture.is_absolute()
  source_manifest=x.owner_fixture;source_manifest_sha=sha(source_manifest)
  fixture=json.loads(source_manifest.read_text());source_root=pathlib.Path(fixture["source_root"])
  assert source_root.is_absolute() and not source_root.is_relative_to(ROOT)
  assert fixture["patch_sha256"]=="3aebc61f1a1979d4e36d669e3c33f5ae8c848d38a3ca0574c62329bdc154bbff"
  assert sha(pathlib.Path(fixture["patch_path"]))==fixture["patch_sha256"]
  assert fixture["base_closure_source_sha256"]==graph["closure_source_sha256"]
  assert fixture["changed_file"]=="Solidity/Hash/CollisionBound.lean" and not fixture["production_sources_edited"]
  assert set(fixture["tree_sha256"])==set(fixture["original_tree_sha256"])
  assert [p for p in fixture["tree_sha256"] if fixture["tree_sha256"][p]!=fixture["original_tree_sha256"][p]]==[fixture["changed_file"]]
  assert frozen_matches(ROOT,fixture["original_tree_sha256"])
  source_tree=fixture["tree_sha256"];assert frozen_matches(source_root,source_tree)
  validate_postimage(source_root/fixture["changed_file"])
  compiled_hashes={m:source_tree[m.replace(".","/")+".lean"] for m in graph["build_order"]}
 assert len(pathlib.Path("/proc/swaps").read_text().splitlines())==1,"swap active"
 assert available()>=RESERVE
 no_competing_lean()
 assert not json.loads(cmd(["ps","--format","{{json .}}","--filter","status=running"]).decode() or "null"),"another container running"
 assert x.image.startswith("sha256:"),"require immutable local image ID"
 archive=x.toolchain.with_name(x.toolchain.name+".tar.zst")
 archive_sha=sha(archive)
 if "4.35.0" in x.toolchain.name:
  pin=json.loads(pathlib.Path("/workspace/h62-coordinator-inputs/toolchain-pin.json").read_text())
  assert archive_sha==pin["sha256"],"coordinator archive pin mismatch"
 else:assert "4.24.0" in x.toolchain.name,"unassigned toolchain"
 x.output.mkdir();(x.output/"artifacts").mkdir();(x.output/"logs").mkdir()
 for m in graph["build_order"]:(x.output/"artifacts"/pathlib.Path(m.replace(".","/"))).parent.mkdir(parents=True,exist_ok=True)
 profile=["create","--name","migrate-storage-"+x.output.name,"--network=none","--memory="+str(LIMIT),"--memory-swap="+str(LIMIT),"--cpus=1","--cap-drop=ALL","--security-opt=no-new-privileges","--user",str(os.getuid())+":"+str(os.getgid()),"-e","LEAN_NUM_THREADS=1","-e","LEAN_PATH=/out/artifacts","--mount","type=bind,src="+str(source_root)+",dst=/src,readonly","--mount","type=bind,src="+str(x.toolchain)+",dst=/toolchain,readonly","--mount","type=bind,src="+str(x.output)+",dst=/out","-w","/src",x.image,"sleep","infinity"]
 cid=cmd(profile,text=True).strip();result={"container":cid,"profile":profile,"modules":[],"component_only":True,"cache":"empty output dir; direct Lean; no Lake artifact or per-master cache; OS page cache not normalized","archive":{"path":str(archive),"sha256":archive_sha},"limits":{"memory":LIMIT,"memory_swap_total":LIMIT,"cpus":1,"reserve":RESERVE,"lean_threads":1},"closure_source_sha256":compiled_hashes,"base_closure_source_sha256":graph["closure_source_sha256"],"source_root":str(source_root),"source_tree_sha256":source_tree,"source_manifest":str(source_manifest) if source_manifest else None,"source_manifest_sha256":source_manifest_sha,"controls_sha256":{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [pathlib.Path(__file__),pathlib.Path(__file__).with_name("census.py"),pathlib.Path(__file__).with_name("prepare_owner_overlay.py"),x.toolchain/"bin/lean",x.toolchain/"bin/lake"]}}
 (x.output/"profile.json").write_text(json.dumps(result,indent=2))
 start=time.monotonic();reason=None
 for sig in [signal.SIGTERM,signal.SIGHUP,signal.SIGINT]:signal.signal(sig,interrupted)
 try:
  cmd(["start",cid]);j=json.loads(cmd(["inspect",cid]))[0]
  assert j["HostConfig"]["Memory"]==LIMIT and j["HostConfig"]["MemorySwap"]==LIMIT and j["HostConfig"]["NanoCpus"]==1000000000
  for exe in ["lean","lake"]:
   result[exe+"_version"]=cmd(["exec",cid,"/toolchain/bin/"+exe,"--version"],text=True).strip();print(result[exe+"_version"],flush=True)
  build_start=time.monotonic()
  for i,m in enumerate(graph["build_order"]):
   rel=m.replace(".","/");argv=["exec",cid,"/toolchain/bin/lean","-j1","--tstack=131072","-M10240","-o","/out/artifacts/"+rel+".olean","-i","/out/artifacts/"+rel+".ilean","/src/"+rel+".lean"]
   t=time.monotonic();peak=0;rss_peak=0;minimum=available();stop=None
   with (x.output/"logs"/(m+".log")).open("wb") as f:
    proc=subprocess.Popen(D+argv,env=ENV,stdout=f,stderr=subprocess.STDOUT)
    while proc.poll() is None:
     # Docker top reports aggregate resident memory of this private cgroup.
     top=cmd(["top",cid,"-eo","pid,comm,rss"],text=True).splitlines()[1:]
     rows=[line.split() for line in top];rss=sum(int(row[-1])*1024 for row in rows);rss_peak=max(rss_peak,rss)
     assert sum(row[1]=="lean" for row in rows)<=1,"nonserial Lean"
     no_competing_lean(cid)
     minimum=min(minimum,available())
     if minimum<RESERVE:stop="4GiB reserve violated"
     if rss>LIMIT:stop="RSS limit violated"
     if time.monotonic()-t>x.timeout:stop="module wall timeout"
     if stop:
      cmd(["kill",cid]);break
     time.sleep(.1)
    rc=proc.wait()
   rec={"module":m,"command":D+argv,"exit":rc,"wall_seconds":time.monotonic()-t,"peak_sampled_aggregate_rss_bytes":rss_peak,"minimum_available_bytes":minimum,"stop":stop}
   result["modules"].append(rec);(x.output/"progress.json").write_text(json.dumps(result,indent=2));print(m,rc,round(rec["wall_seconds"],3),rss_peak,flush=True)
   if rc or stop:raise RuntimeError("failed "+m+": "+str(stop or rc))
   if m=="Solidity.KeySort":print("KEYSORT_COMPONENT_PASS",flush=True)
  result["build_wall_seconds"]=time.monotonic()-build_start
 except BaseException as e:reason=type(e).__name__+": "+str(e)
 finally:
  result["controller_wall_seconds"]=time.monotonic()-start;result["reason"]=reason
  result["exit"]=0 if reason is None else 1
  for sig in [signal.SIGTERM,signal.SIGHUP,signal.SIGINT]:signal.signal(sig,signal.SIG_IGN)
  try:
   j=json.loads(cmd(["inspect",cid]))[0]
   if j["State"]["Running"]:cmd(["kill",cid])
   result["runtime_after"]=json.loads(cmd(["inspect",cid]))[0]["State"]
   assert not result["runtime_after"]["Running"],"cleanup failed"
   after=census();result["sources_unchanged"]=graph==after and after["closure_matches_checkout"]
   result["fixture_sources_unchanged"]=frozen_matches(source_root,source_tree) and (source_manifest is None or sha(source_manifest)==source_manifest_sha)
   result["controls_unchanged"]=all(sha(pathlib.Path(p))==h for p,h in result["controls_sha256"].items())
   if not result["sources_unchanged"] or not result["controls_unchanged"] or not result["fixture_sources_unchanged"]:result["exit"]=1
  except BaseException as e:
   result["exit"]=1;result["cleanup_error"]=str(e)
  result["peak_sampled_aggregate_rss_bytes"]=max((m["peak_sampled_aggregate_rss_bytes"] for m in result["modules"]),default=0)
  (x.output/"result.json").write_text(json.dumps(result,indent=2));print("COMPONENT_RESULT",result["exit"],reason,flush=True)
 return result["exit"]
if __name__=="__main__":raise SystemExit(main())
