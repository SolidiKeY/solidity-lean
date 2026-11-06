#!/usr/bin/env python3
"""Bounded backfill fixture run in a stopped measurement runtime; no full gate."""
import fcntl,json,pathlib,signal,subprocess,sys,time
from measure import cmd,available,no_competing_lean,RESERVE,LIMIT,interrupted,ENV,sha
from census import ROOT,frozen_matches
run=pathlib.Path(sys.argv[1]);fixture=pathlib.Path(sys.argv[2]);out=pathlib.Path(sys.argv[3]);assert run.is_absolute() and out.is_absolute() and not out.exists()
assert str(fixture).startswith("tests/h62/item6/migrate-storage/") and (ROOT/fixture).is_file()
lock=open("/tmp/solidity-lean-feature-groups-20261025/writer.lock","r+");fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
no_competing_lean();assert available()>=RESERVE
profile=json.loads((run/"profile.json").read_text());cid=profile["container"];j=json.loads(cmd(["inspect",cid]))[0]
assert not j["State"]["Running"] and j["HostConfig"]["Memory"]==LIMIT and j["HostConfig"]["MemorySwap"]==LIMIT and j["HostConfig"]["NanoCpus"]==1000000000
for sig in [signal.SIGTERM,signal.SIGINT,signal.SIGHUP]:signal.signal(sig,interrupted)
argv=["exec",cid,"/toolchain/bin/lean","-j1","--tstack=131072","-M10240","/src/"+str(fixture)]
controls={str(p):sha(p) for p in [pathlib.Path(__file__),ROOT/"scripts/h62/item6/migrate-storage/measure.py",ROOT/"scripts/h62/item6/migrate-storage/census.py",ROOT/"scripts/h62/item6/migrate-storage/prepare_owner_overlay.py",ROOT/fixture]}
source_root=pathlib.Path(profile.get("source_root",ROOT))
compiled=profile.get("source_tree_sha256",{m.replace(".","/")+".lean":h for m,h in profile["closure_source_sha256"].items()})
originals={m.replace(".","/")+".lean":h for m,h in profile.get("base_closure_source_sha256",profile["closure_source_sha256"]).items()}
assert frozen_matches(source_root,compiled)
assert (source_root/fixture).read_bytes()==(ROOT/fixture).read_bytes()
controls[str(source_root/fixture)]=sha(source_root/fixture)
assert frozen_matches(ROOT,originals)
result={"runtime_image":j["Image"],"archive":profile["archive"],"controls_sha256":controls,"command":argv,"source":str(fixture),"component_only":True,"source_sha256":sha(ROOT/fixture),"measurement_profile_sha256":sha(run/"profile.json")};start=time.monotonic()
try:
 cmd(["start",cid])
 for exe in ["lean","lake"]:result[exe+"_version"]=cmd(["exec",cid,"/toolchain/bin/"+exe,"--version"],text=True).strip()
 with out.open("wb") as f:
  proc=subprocess.Popen(["docker","--host=unix:///var/run/docker.sock"]+argv,stdout=f,stderr=subprocess.STDOUT,env=ENV)
  peak=0
  while proc.poll() is None:
   no_competing_lean(cid);assert available()>=RESERVE
   rows=[s.split() for s in cmd(["top",cid,"-eo","pid,comm,rss"],text=True).splitlines()[1:]]
   assert sum(r[1]=="lean" for r in rows)<=1
   peak=max(peak,sum(int(r[-1])*1024 for r in rows));assert peak<=LIMIT
   assert time.monotonic()-start<120,"fixture wall bound"
   time.sleep(.1)
  result.update(exit=proc.wait(),wall_seconds=time.monotonic()-start,peak_sampled_rss_bytes=peak)
except BaseException as e:result.update(exit=1,reason=str(e))
finally:
 for sig in [signal.SIGTERM,signal.SIGINT,signal.SIGHUP]:signal.signal(sig,signal.SIG_IGN)
 try:
  j=json.loads(cmd(["inspect",cid]))[0]
  if j["State"]["Running"]:cmd(["kill",cid])
  assert not json.loads(cmd(["inspect",cid]))[0]["State"]["Running"]
  result["cleanup_stopped"]=True
  result["controls_unchanged"]=all(sha(pathlib.Path(p))==h for p,h in controls.items())
  result["original_sources_unchanged"]=frozen_matches(ROOT,originals)
  result["compiled_sources_unchanged"]=frozen_matches(source_root,compiled)
  assert result["controls_unchanged"] and result["original_sources_unchanged"] and result["compiled_sources_unchanged"],"input drift"
 except BaseException as e:result.update(exit=1,cleanup_error=str(e))
 out.with_suffix(".result.json").write_text(json.dumps(result,indent=2))
print(json.dumps(result));sys.exit(result["exit"])
