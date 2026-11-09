#!/usr/bin/env python3
"""Deterministic H44 archive from committed metadata and preserved VM evidence."""
import argparse,gzip,hashlib,io,re,subprocess,tarfile
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument("--metadata-revision",required=True);ap.add_argument("--evidence",type=Path,required=True);ap.add_argument("--out",type=Path,required=True);a=ap.parse_args()
prefix="tests/h62/item6/migrate-precompiles/"
paths=subprocess.check_output(["git","ls-tree","-r","--name-only",a.metadata_revision,"--",prefix],text=True).splitlines()
entries={"tracked/"+p:subprocess.check_output(["git","show",a.metadata_revision+":"+p]) for p in paths if not p.endswith(".lean")}
for p in sorted(a.evidence.rglob("*")):
    if p.is_file():entries["evidence/"+p.relative_to(a.evidence).as_posix()]=p.read_bytes()
for data in list(entries.values()):
    for digest,path in re.findall(rb"(?m)^([0-9a-f]{64})  (/[^\n]+)$",data):
        p=Path(path.decode())
        if not p.is_file():raise SystemExit("missing referenced evidence: "+str(p))
        raw=p.read_bytes()
        if hashlib.sha256(raw).hexdigest()!=digest.decode():raise SystemExit("referenced hash mismatch: "+str(p))
        if not p.is_relative_to(a.evidence):entries["referenced/"+str(p).lstrip("/")]=raw
if a.out.exists():raise SystemExit("refuse existing archive")
a.out.parent.mkdir(parents=True,exist_ok=True)
with a.out.open("wb") as raw,gzip.GzipFile(filename="",fileobj=raw,mode="wb",mtime=0) as gz,tarfile.open(fileobj=gz,mode="w") as tar:
    for name,data in sorted(entries.items()):
        info=tarfile.TarInfo(name);info.size=len(data);info.mode=0o644;info.mtime=0
        tar.addfile(info,io.BytesIO(data))
print(hashlib.sha256(a.out.read_bytes()).hexdigest(),a.out)
print("bytes",a.out.stat().st_size,"entries",len(entries))
