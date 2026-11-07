#!/usr/bin/env python3
"""Portable H44 archive/relative manifest. Byte integrity, never a Lean proof.

pack writes bulk data outside Git. verify reads the archive without extracting,
needs neither Lean nor any original VM path, and checks every regular member.
"""
import argparse,fcntl,gzip,hashlib,io,tarfile
from pathlib import Path,PurePosixPath

def safe(name):
 p=PurePosixPath(name)
 if p.is_absolute() or ".." in p.parts or str(p)!=name or not p.parts:
  raise ValueError("unsafe/noncanonical archive path: "+name)
 return name

def digest(stream):
 h=hashlib.sha256()
 for block in iter(lambda:stream.read(1024*1024),b""):h.update(block)
 return h.hexdigest()

def verify(archive,manifest):
 expected={}
 for line in manifest.read_text().splitlines():
  if not line or line.startswith("#"):continue
  value,name=line.split("  ",1);safe(name)
  if name in expected or len(value)!=64:raise ValueError("duplicate/bad manifest entry")
  expected[name]=value
 if not expected:raise ValueError("empty evidence manifest")
 seen=set()
 with tarfile.open(archive,"r:gz") as tar:
  for item in tar:
   name=safe(item.name)
   if not item.isfile() or name in seen or name not in expected:raise ValueError("unexpected/nonregular archive member")
   content=tar.extractfile(item)
   if digest(content)!=expected[name]:raise ValueError("checksum mismatch: "+name)
   seen.add(name)
 if seen!=set(expected):raise ValueError("missing archive members")
 return len(seen)

def pack(evidence,archive,manifest):
 root=Path(__file__).resolve().parents[4]
 evidence=evidence.resolve();archive=archive.resolve();manifest=manifest.resolve()
 if any(p.is_relative_to(root) for p in (evidence,archive,manifest)):raise ValueError("H44 bulk and per-member manifests must stay outside Git")
 with open("/tmp/solidity-lean-feature-groups-20261025/writer.lock","a") as lock:
  fcntl.flock(lock,fcntl.LOCK_EX)
  files=[]
  exported={"original.patch","audit-abi-world.bundle","evidence.tar.gz","handoff.md","retirement-status.json","SHA256SUMS","sha256-manifest.txt"}
  for p in evidence.rglob("*"):
   rel=p.relative_to(evidence)
   if "node_modules" in rel.parts or "artifacts" in rel.parts:continue
   if len(rel.parts)==1 and rel.name in exported:continue
   if p==archive or p==manifest or p.is_symlink() or not p.is_file():continue
   files.append((safe(rel.as_posix()),p))
  archive.parent.mkdir(parents=True,exist_ok=True);rows=[]
  with archive.open("wb") as raw,gzip.GzipFile(filename="",mode="wb",fileobj=raw,mtime=0) as gz,tarfile.open(fileobj=gz,mode="w") as tar:
   for name,p in sorted(files):
    data=p.read_bytes();info=tarfile.TarInfo(name);info.size=len(data);info.mode=0o644;info.mtime=0
    tar.addfile(info,io.BytesIO(data));rows.append(hashlib.sha256(data).hexdigest()+"  "+name+"\n")
  manifest.write_text("# Paths relative to the unpacked evidence archive root; no original VM required\n"+"".join(rows))
 return verify(archive,manifest)

if __name__=="__main__":
 p=argparse.ArgumentParser();p.add_argument("mode",choices=("pack","verify"));p.add_argument("--archive",type=Path,required=True);p.add_argument("--manifest",type=Path,required=True);p.add_argument("--evidence",type=Path);a=p.parse_args()
 if a.mode=="pack":
  if a.evidence is None:p.error("pack requires --evidence")
  count=pack(a.evidence,a.archive,a.manifest)
 else:count=verify(a.archive,a.manifest)
 print("PASS: "+str(count)+" archive-relative evidence files verified; no Lean invoked")
