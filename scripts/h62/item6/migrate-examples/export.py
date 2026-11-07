#!/usr/bin/env python3
"""Export committed overlay and small evidence; keep build/cache bulk off Git."""
import argparse,fcntl,gzip,hashlib,io,json,pathlib,subprocess,tarfile
def file_sha256(path):
    with path.open("rb") as stream:return hashlib.file_digest(stream,"sha256").hexdigest()

p=argparse.ArgumentParser();p.add_argument("--evidence",type=pathlib.Path,required=True);a=p.parse_args();e=a.evidence.resolve()
lock=open("/tmp/solidity-lean-feature-groups-20261025/writer.lock","a")
fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
branch=subprocess.check_output(["git","branch","--show-current"],text=True).strip()
assert branch=="codex/solidity-h62-6-20261106/migrate-examples",branch
assert not subprocess.check_output(["git","status","--porcelain"],text=True),"commit checkpoint before exporting"
base="c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
subprocess.run(["git","merge-base","--is-ancestor",base,"HEAD"],check=True)
# Scope the cumulative patch after upstream integration: the bundle retains
# ancestry, while the review patch must not attribute other lanes' changes here.
scope=subprocess.check_output(["git","ls-tree","-r","--name-only",base,"--","Solidity/Examples"],text=True).splitlines()
scope=[path for path in scope if path.endswith(".lean")]
assert len(scope)==354,"frozen original scope changed"
patch_paths=["scripts/h62/item6/migrate-examples","tests/h62/item6/migrate-examples","docs/feature-work/h62-6-migrate-examples.md"]+scope
head=subprocess.check_output(["git","rev-parse","HEAD"],text=True).strip()
(e/"committed-state.json").write_text(json.dumps({"head":head,"base":base,"branch":branch,"repository":str(pathlib.Path.cwd().resolve()),"patch_boundary":"cumulative committed diff restricted to original assigned paths; bundle also includes integrated upstream ancestry","original_example_files":len(scope)},indent=2)+"\n")
(e/"handoff.md").write_bytes(pathlib.Path("docs/feature-work/h62-6-migrate-examples.md").read_bytes())
(e/"original.patch").write_bytes(subprocess.check_output(["git","diff","--binary","--full-index",base,head,"--",*patch_paths]))
bundle=e/("overlay-"+head+".bundle")
if not bundle.exists():subprocess.run(["git","bundle","create",str(bundle),branch,"^"+base],check=True)
census=json.loads((e/"census-base.json").read_text())
(e/"source-base.sha256").write_text("".join(row["source_sha256"]+"  "+row["path"]+"\n" for row in census["modules"]))
files=sorted(x for x in e.iterdir() if x.is_file() and x.name not in ("SHA256SUMS","evidence.tar.gz") and x.suffix in (".json",".jsonl",".lean",".log",".md",".txt",".sha256",".patch",".bundle"))
# Normalized tar metadata makes a snapshot reproducible given its input bytes.
with (e/"evidence.tar.gz").open("wb") as raw_archive, gzip.GzipFile(filename="",mode="wb",fileobj=raw_archive,mtime=0) as gz, tarfile.open(fileobj=gz,mode="w") as tar:
    for f in files:
        info=tarfile.TarInfo(f.name);info.size=f.stat().st_size;info.mode=0o644;info.mtime=0
        with f.open("rb") as stream:tar.addfile(info,stream)
files.append(e/"evidence.tar.gz")
(e/"SHA256SUMS").write_text("".join(file_sha256(f)+"  "+f.name+"\n" for f in sorted(files)))
print(json.dumps({"head":head,"base":base,"patch":str(e/"original.patch"),"bundle":str(bundle),"archive":str(e/"evidence.tar.gz"),"checksums":str(e/"SHA256SUMS")}))
