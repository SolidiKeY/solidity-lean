"""Restore exact raw captures from the committed, checksummed gzip evidence."""
import gzip, hashlib, json, pathlib
root=pathlib.Path.cwd()
base=root/"docs/benchmarks/directruntime-2026-11-04"
records=json.loads((base/"raw-captures.json").read_text())
for row in records:
 archive=root/row["archive"]
 raw=root/row["raw"]
 assert raw.resolve().is_relative_to(base.resolve())
 packed=archive.read_bytes()
 assert hashlib.sha256(packed).hexdigest()==row["archiveSha256"]
 data=gzip.decompress(packed)
 assert hashlib.sha256(data).hexdigest()==row["rawSha256"]
 if raw.exists():
  assert raw.read_bytes()==data, "Existing capture differs; refusing overwrite: "+str(raw)
 else:
  raw.parent.mkdir(parents=True,exist_ok=True)
  with raw.open("xb") as output:output.write(data)
print("PASS restored/verified",len(records),"exact raw captures")
