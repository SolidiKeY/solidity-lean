#!/usr/bin/env python3
"""Verify QLEAN-CACHE archive, exact BASE sources and materialized import closure; no Lean.
python3 docs/audits/direction-tools/mutation/verify_cache.py --archive ARCHIVE --extracted DIRECTORY
"""
import argparse,hashlib,json,re,sys,tarfile
from pathlib import Path
sys.dont_write_bytecode=True
from base_tree import BASE,read_base_blobs
OUT=Path(__file__).resolve().parent
ARCHIVE_SHA="cf045686365b3f1dab6769dd022e91a296c08f4750291e46dbd5a8b2269961ad"
PUBLISHER="71175a9a62cbb2440d5acd5d5d28ab0a7d5f34be"
def sha(data):return hashlib.sha256(data).hexdigest()
def file_sha(path):
 h=hashlib.sha256()
 with path.open("rb") as f:
  for block in iter(lambda:f.read(1024*1024),b""):h.update(block)
 return h.hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument("--archive",type=Path,required=True);ap.add_argument("--extracted",type=Path,required=True);a=ap.parse_args()
 assert a.archive.stat().st_size==330790747 and file_sha(a.archive)==ARCHIVE_SHA
 with tarfile.open(a.archive,"r:gz") as archive:
  members=archive.getmembers();names=[m.name for m in members];assert len(names)==len(set(names))
  assert all(not Path(n).is_absolute() and ".." not in Path(n).parts for n in names)
  assert all(m.isfile() or m.isdir() for m in members)
  manifest_bytes=archive.extractfile("manifest.json").read()
  publisher_bytes=archive.extractfile("publisher-build.out").read()
 assert (a.extracted/"manifest.json").read_bytes()==manifest_bytes
 assert (a.extracted/"publisher-build.out").read_bytes()==publisher_bytes
 manifest=json.loads(manifest_bytes);assert manifest["base"]==BASE and manifest["publisher_head"]==PUBLISHER and manifest["toolchain"]=="leanprover/lean4:v4.24.0"
 modules={m["module"]:m for m in manifest["modules"]};assert len(modules)==len(manifest["modules"])==264
 assert "Solidity.Calculus.Closers" not in modules,"mutated module must not come from import cache"
 root_source="Solidity/Calculus/Closers.lean";sources=read_base_blobs([m["source"] for m in modules.values()]+[root_source])
 artifacts={};traces={}
 for name,m in modules.items():
  assert m["source"]==name.replace(".","/")+".lean"
  assert sha(sources[m["source"]])==m["source_sha256"],m["source"]
  trace_path="traces/"+name.replace(".","/")+".trace";trace_bytes=(a.extracted/trace_path).read_bytes();assert sha(trace_bytes)==m["trace_sha256"]
  trace=json.loads(trace_bytes);assert str(trace["depHash"])==str(m["depHash"])
  hashes={str(h) for v in trace["outputs"].values() for h in (v if isinstance(v,list) else [v])}
  traces[trace_path]=m["trace_sha256"]
  for item in m["artifacts"]:
   path=item["path"];assert path.startswith("lib/") and ".." not in Path(path).parts
   target=a.extracted/path;assert not target.is_symlink() and target.stat().st_size==item["bytes"] and file_sha(target)==item["sha256"],path
   assert str(item["lake_output_hash"]) in hashes
   artifacts[path.removeprefix("lib/")]=item["sha256"]
 def imports(blob):
  return [name for line in blob.decode().splitlines() if line.startswith("import ") for name in line.split("--",1)[0].split()[1:] if name.startswith("Solidity.")]
 seen=set();pending=imports(sources[root_source])
 while pending:
  name=pending.pop()
  if name in seen:continue
  assert name in modules,"missing transitive import "+name
  seen.add(name);pending.extend(imports(sources[modules[name]["source"]]))
 assert seen==set(modules)
 assert "Solidity/Calculus/CloseCallSharing.olean" in artifacts
 actual={str(p.relative_to(a.extracted/"lib")) for p in (a.extracted/"lib").rglob("*") if p.is_file()}
 assert actual==set(artifacts),"unlisted or missing cache files"
 assert not any(p.is_symlink() for p in (a.extracted/"lib").rglob("*"))
 result=dict(status="pass",base=BASE,archive_sha256=ARCHIVE_SHA,manifest_sha256=sha(manifest_bytes),publisher_head=PUBLISHER,cache_root=str((a.extracted/"lib").resolve()),modules_verified=len(modules),sources_verified=len(modules),traces_verified=len(traces),artifacts_verified=len(artifacts),artifacts=artifacts,source_bindings={m["source"]:m["source_sha256"] for m in modules.values()},publisher_build_sha256=file_sha(a.extracted/"publisher-build.out"),boundary="Reuse of existing published compiled imports with BASE source/trace/artifact bindings; no new kernel replay, build, differential execution or elaboration performed")
 data=json.dumps(result,indent=2,sort_keys=True)+"\n";assert len(data.encode())<1000000;(OUT/"cache-verification.json").write_text(data)
 print(json.dumps({k:v for k,v in result.items() if k not in ("artifacts","source_bindings")},sort_keys=True))
if __name__=="__main__":main()
