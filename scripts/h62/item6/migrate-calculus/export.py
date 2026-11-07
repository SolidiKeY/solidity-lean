#!/usr/bin/env python3
"""Export committed review artifacts and SHA256 inventory; never publishes or gates."""
import argparse, fcntl, hashlib, json, os, subprocess
from pathlib import Path
BASE="c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
def git(root,*args):return subprocess.check_output(["git","-C",str(root),*args])
def sha(path):
    h=hashlib.sha256()
    with path.open("rb") as stream:
        while data:=stream.read(1024*1024):h.update(data)
    return h.hexdigest()
def main():
    parser=argparse.ArgumentParser();parser.add_argument("root");parser.add_argument("evidence");args=parser.parse_args()
    root=Path(args.root).resolve();evidence=Path(args.evidence).resolve();out=evidence/"handoff";out.mkdir(parents=True,exist_ok=True)
    lock=open("/tmp/solidity-lean-feature-groups-20261025/writer.lock","a");fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    if git(root,"status","--porcelain").strip():raise RuntimeError("Commit/preserve task changes before export")
    head=git(root,"rev-parse","HEAD").decode().strip();branch=git(root,"branch","--show-current").decode().strip()
    if branch!="codex/solidity-h62-6-20261106/migrate-calculus":raise RuntimeError("Wrong branch")
    subprocess.run(["git","-C",str(root),"merge-base","--is-ancestor",BASE,head],check=True)
    changed=git(root,"diff","--name-only",BASE,head).decode().splitlines()
    allowed=set(git(root,"ls-tree","-r","--name-only",BASE,"Solidity/Calculus").decode().splitlines())
    if any(not (p in allowed or p=="docs/feature-work/h62-6-migrate-calculus.md" or p.startswith(("scripts/h62/item6/migrate-calculus/","tests/h62/item6/migrate-calculus/"))) for p in changed):raise RuntimeError("Out-of-scope committed path")
    (out/"original.patch").write_bytes(git(root,"format-patch","--stdout","--binary",BASE+".."+head))
    bundle=out/"migrate-calculus.bundle"
    if bundle.exists():raise RuntimeError("Preserve prior bundle; choose a fresh evidence export directory")
    subprocess.run(["git","-C",str(root),"bundle","create",str(bundle),BASE+"..HEAD"],check=True)
    verify=subprocess.run(["git","-C",str(root),"bundle","verify",str(bundle)],check=True,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (out/"bundle-verify.log").write_text(verify.stdout)
    metadata=dict(status="blocked",goal_complete=False,base=BASE,head=head,branch=branch,repository=str(root),changed=changed,original_patch=str(out/"original.patch"),bundle=str(bundle),frozen_production_files_changed=[p for p in changed if p.startswith("Solidity/")])
    (out/"manifest.json").write_text(json.dumps(metadata,indent=2)+"\n")
    (out/"HANDOFF.md").write_text((root/"docs/feature-work/h62-6-migrate-calculus.md").read_text()+"\n## Export identity\n\n"+json.dumps(metadata,indent=2)+"\n")
    paths=sorted(evidence.rglob("*"));links={str(path.relative_to(evidence)):os.readlink(path) for path in paths if path.is_symlink()}
    (out/"symlinks.json").write_text(json.dumps(links,indent=2,sort_keys=True)+"\n")
    checksums=out/"SHA256SUMS"
    rows=[]
    for path in sorted(evidence.rglob("*")):
        if path==checksums or path.is_symlink() or not path.is_file():continue
        rows.append(sha(path)+"  "+str(path)+"\n")
    checksums.write_text("".join(rows))
    print(json.dumps(dict(**metadata,handoff=str(out/"HANDOFF.md"),evidence=str(evidence),checksums=str(checksums),checksums_sha256=sha(checksums),files_hashed=len(rows))))
if __name__=="__main__":main()
