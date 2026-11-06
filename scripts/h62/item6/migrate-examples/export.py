#!/usr/bin/env python3
"""Export committed overlay and small evidence; keep build/cache bulk off Git."""
import argparse,hashlib,io,json,pathlib,subprocess,tarfile
p=argparse.ArgumentParser();p.add_argument("--evidence",type=pathlib.Path,required=True);a=p.parse_args();e=a.evidence.resolve()
base="c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
head=subprocess.check_output(["git","rev-parse","HEAD"],text=True).strip()
(e/"original.patch").write_bytes(subprocess.check_output(["git","format-patch","--stdout",base+".."+head]))
bundle=e/("overlay-"+head+".bundle")
if not bundle.exists():subprocess.run(["git","bundle","create",str(bundle),base+".."+head],check=True)
census=json.loads((e/"census-base.json").read_text())
(e/"source-base.sha256").write_text("".join(row["source_sha256"]+"  "+row["path"]+"\n" for row in census["modules"]))
files=sorted(x for x in e.iterdir() if x.is_file() and x.name not in ("SHA256SUMS","evidence.tar.gz") and x.suffix in (".json",".log",".md",".txt",".sha256",".patch",".bundle"))
# Normalized tar metadata makes a snapshot reproducible given its input bytes.
with tarfile.open(e/"evidence.tar.gz","w:gz") as tar:
    for f in files:
        raw=f.read_bytes();info=tarfile.TarInfo(f.name);info.size=len(raw);info.mode=0o644;info.mtime=0;tar.addfile(info,io.BytesIO(raw))
files.append(e/"evidence.tar.gz")
(e/"SHA256SUMS").write_text("".join(hashlib.sha256(f.read_bytes()).hexdigest()+"  "+str(f)+"\n" for f in sorted(files)))
print(json.dumps({"head":head,"base":base,"patch":str(e/"original.patch"),"bundle":str(bundle),"archive":str(e/"evidence.tar.gz"),"checksums":str(e/"SHA256SUMS")}))
