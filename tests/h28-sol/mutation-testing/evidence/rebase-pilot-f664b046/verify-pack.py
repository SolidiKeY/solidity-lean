from pathlib import Path
import hashlib,json,tarfile,time
out=Path(__file__).resolve().parent
receipt=json.loads((out/"cache-pack.json").read_text())
catalog=json.loads((out/"catalog.json").read_text())
def sha(f):
 h=hashlib.sha256()
 for b in iter(lambda:f.read(1048576),b""):h.update(b)
 return h.hexdigest()
t=time.monotonic()
with open(receipt["archive"],"rb") as f:assert sha(f)==receipt["sha256"]
expected={"sources/"+p:h for p,h in catalog["sources"].items()}
with tarfile.open(receipt["archive"],"r:gz") as tar:
 for line in tar.extractfile("run/SHA256SUMS").read().decode().splitlines():
  h,n=line.split("  ",1);expected["run/"+n]=h
 seen=set()
 metadata={"run/SHA256SUMS","catalog.json","README.md"}
 for member in tar:
  if member.isdir():continue
  assert member.isfile() and member.name not in seen
  assert not member.name.startswith("/") and ".." not in Path(member.name).parts
  seen.add(member.name)
  if member.name in expected:assert sha(tar.extractfile(member))==expected[member.name],member.name
 assert seen==set(expected)|metadata
 assert tar.extractfile("catalog.json").read()==(out/"catalog.json").read_bytes()
with open(receipt["dependency_pack"]["archive"],"rb") as f:assert sha(f)==receipt["dependency_pack"]["sha256"]
print(json.dumps({"status":"pass","command":"python3 -B "+str(Path(__file__).resolve()),"archive":receipt["archive"],"regular_members":len(seen),"compiled_artifacts":len(catalog["compiled_artifacts"]),"dependency_pack_hash_verified":True,"seconds":time.monotonic()-t,"coordinator_pull_observed":False},indent=2))
