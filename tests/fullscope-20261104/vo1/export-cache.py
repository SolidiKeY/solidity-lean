#!/usr/bin/env python3
"""Export current optimizer/KeySort dependency artifacts without claiming delivery.
Lake input mappings and content-addressed artifacts are retained for cache reuse.
"""
from pathlib import Path
import fcntl, hashlib, json, re, subprocess, tarfile, sys
root=Path(__file__).resolve().parents[3]
lock=open("/tmp/solidity-lean-feature-groups-20261025/writer.lock","a")
fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
delivery=root/"tests/fullscope-20261104/vo1/delivery"
if len(sys.argv)>2:raise SystemExit("usage: export-cache.py [FRESH-OWNED-DELIVERY-DIRECTORY]")
requested=Path(sys.argv[1]) if len(sys.argv)==2 else delivery
if not requested.is_absolute():requested=root/requested
out=requested.resolve()
if delivery.resolve()!=delivery or requested.is_symlink() or (out!=delivery and out.parent!=delivery):
 raise SystemExit("Refuse symlink/escaping destination; use a direct owned delivery subdirectory")
if out.exists() and (not out.is_dir() or any(out.iterdir())):
 raise SystemExit("Preserve nonempty export directory; choose a fresh delivery subdirectory")
out.mkdir(exist_ok=True)
status=out/"export-status.json"
status.write_text(json.dumps(dict(status="incomplete",meaning="Preserve this directory if export fails; retry in a fresh directory"))+"\n")
cache=Path("/workspace/.setup/cache/lake")
def digest(p):
 h=hashlib.sha256()
 with p.open("rb") as f:
  for chunk in iter(lambda:f.read(1024*1024),b""): h.update(chunk)
 return h.hexdigest()
mods=set()
def visit(m):
 p=root/(m.replace(".","/")+".lean")
 if m in mods or not p.is_file():return
 mods.add(m)
 for dep in re.findall(r"^import (\S+)",p.read_text(),re.M):visit(dep)
visit("Solidity.Optimizer.Controls");visit("SolkeyCheck")
fixture_sources=[];fixture_receipts={}
fixture_specs=[
 ("ValueValidatorControls.lean","rebasee684-value-kernel.json"),
 ("YulValidatorControls.lean","rebasee684-yul-kernel.json"),
 ("PipelineControls.lean","rebasee684-pipeline-kernel.json")]
for filename,receipt_name in fixture_specs:
 fixture=root/"tests/fullscope-20261104/vo1"/filename
 if not fixture.is_file():continue
 receipt_path=root/"tests/fullscope-20261104/vo1/evidence"/receipt_name
 if not receipt_path.is_file():raise SystemExit("Missing per-file fixture kernel receipt: "+filename)
 receipt=json.loads(receipt_path.read_text())
 if receipt.get("runner_exit")!=0 or not receipt.get("source_unchanged") or not receipt.get("cleanup_verified"):
  raise SystemExit("Fixture kernel receipt is not a passing bounded source-stable check")
 required_inputs={str(fixture.relative_to(root)),"tests/fullscope-20261104/vo1/runtime.toml","lean-toolchain","lakefile.toml"}
 if not required_inputs<=set(receipt.get("source_sha256",{})):
  raise SystemExit("Fixture kernel receipt lacks critical source/config identities")
 for name,expected in receipt["source_sha256"].items():
  if name.endswith((".lean",".toml")) or name=="lean-toolchain":
   source=root/name
   if not source.is_file() or digest(source)!=expected:raise SystemExit("Kernel input changed: "+name)
 fixture_sources.append(fixture)
 fixture_receipts[str(fixture.relative_to(root))]=dict(receipt=str(receipt_path.relative_to(root)),sha256=digest(receipt_path),checked_head=receipt["head"],command=receipt["command"],log_sha256=receipt["log_sha256"],meaning="per-file kernel checked; no fixture olean claimed")
 for dep in re.findall(r"^import (\S+)",fixture.read_text(),re.M):visit(dep)
files={}; inputs=set(); required_mappings={}; required_artifacts={}
for source in fixture_sources:files["checkout/"+str(source.relative_to(root))]=source
for information in fixture_receipts.values():
 receipt_path=root/information["receipt"]
 files["checkout/"+information["receipt"]]=receipt_path
 log=receipt_path.with_suffix(".log")
 if not log.is_file() or digest(log)!=information["log_sha256"]:raise SystemExit("Missing or changed fixture kernel output log")
 files["checkout/"+str(log.relative_to(root))]=log
for m in sorted(mods):
 rel=m.replace(".","/")
 source=root/(rel+".lean");files["checkout/"+rel+".lean"]=source
 for area in ("lib/lean","ir"):
  prefix=root/".lake/build"/area/rel
  for p in prefix.parent.glob(prefix.name+".*"):
   if p.is_file():files["checkout/"+str(p.relative_to(root))]=p
 trace=root/".lake/build/lib/lean"/(rel+".trace")
 if not trace.is_file():raise SystemExit("Missing checked trace: "+m)
 data=json.loads(trace.read_text());inputs.add(data["depHash"])
 required_mappings[data["depHash"]]=data["outputs"]
 for kind,value in data["outputs"].items():
  suffix={"o":".olean","i":".ilean","c":".c"}.get(kind)
  if suffix is None:raise SystemExit("Unsupported trace output kind; preserve and inspect: "+kind)
  for h in value if isinstance(value,list) else [value]:required_artifacts[str(h)+suffix]=m
for filename,module in required_artifacts.items():
 p=cache/"artifacts"/filename
 if not p.is_file():raise SystemExit("Missing required cached artifact for "+module+": "+filename)
 files["cache/artifacts/"+p.name]=p
mapping=out/"optimizer-inputs.jsonl"
lines=[]; covered=set()
for line in (cache/"inputs/solidity-lean.jsonl").read_text().splitlines():
 key,outputs=json.loads(line)
 if key in inputs:
  if outputs!=required_mappings[key]:raise SystemExit("Conflicting required cache mapping: "+key)
  covered.add(key);lines.append(line)
if covered!=inputs:raise SystemExit("Missing required input mappings: "+repr(sorted(inputs-covered)))
mapping.write_text("\n".join(lines)+"\n")
files["cache/inputs/solidity-lean.jsonl"]=mapping
for rel in ("lean-toolchain","lakefile.toml","lake-manifest.json","tests/fullscope-20261104/vo1/runtime.toml"):
 p=root/rel
 if p.is_file():files["checkout/"+rel]=p
for p in (root/".lake/build/bin").glob("solkeycheck*"):
 if p.is_file():files["checkout/"+str(p.relative_to(root))]=p
external={}
for p in [Path("/workspace/.setup/tools/lean-4.24.0-linux/bin/lean"),Path("/workspace/.setup/tools/lean-4.24.0-linux/bin/lake"),Path("/workspace/.setup/solkey/keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key")]:
 external[str(p)]=digest(p)
record=dict(per_file_fixtures=fixture_receipts,required_cache_artifacts=len(required_artifacts),cache_complete=True,head=subprocess.check_output(["git","rev-parse","HEAD"],cwd=root,text=True).strip(),base="e70b959bf6dd81d09bfaf6eda8025b1cc98bc4c3",modules=sorted(mods),toolchain=(root/"lean-toolchain").read_text().strip(),external_sha256=external,
 provenance="Current source/trace hashes only. Bootstrap cache history UNVERIFIABLE. Export is not transfer receipt or a full-build PASS.",files={n:dict(sha256=digest(p),bytes=p.stat().st_size) for n,p in sorted(files.items())})
manifest=out/"cache-manifest.json";manifest.write_text(json.dumps(record,indent=2)+"\n")
files["cache-manifest.json"]=manifest
archive=out/"cache-packet.tar.zst"
if archive.exists():raise SystemExit("Preserve existing packet; choose a new export directory")
proc=subprocess.Popen(["zstd","-T1","-1","-o",str(archive)],stdin=subprocess.PIPE)
with tarfile.open(fileobj=proc.stdin,mode="w|") as tar:
 for n,p in sorted(files.items()):tar.add(p,arcname=n,recursive=False)
proc.stdin.close()
if proc.wait()!=0:raise SystemExit("cache compression failed")
(out/"cache-packet.sha256").write_text(digest(archive)+"  cache-packet.tar.zst\n")
status.write_text(json.dumps(dict(status="exported",delivery="coordinator-pending",sha256=digest(archive)),indent=2)+"\n")
print(json.dumps(dict(archive=str(archive),sha256=digest(archive),bytes=archive.stat().st_size,modules=len(mods),files=len(files),mappings=len(lines))))
