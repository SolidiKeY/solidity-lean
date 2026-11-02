#!/usr/bin/env bash
set -euo pipefail
exec python3 - "$@" <<'PY'
import hashlib,json,os,pathlib,subprocess,sys,tempfile

def git(*a, **kw): return subprocess.check_output(["git",*map(str,a)],text=True,**kw).strip()
def digest(p):
    h=hashlib.sha256()
    with p.open("rb") as f:
        for b in iter(lambda:f.read(1048576),b""): h.update(b)
    return h.hexdigest()
def files(d): return sorted(p for p in d.rglob("*") if p.is_file())
def verify(d):
    subprocess.run(["sha256sum","-c","--strict","SHA256SUMS"],cwd=d,check=True)
    m=json.loads((d/"manifest.json").read_text()); expected=[]
    for p in files(d):
        rel=p.relative_to(d).as_posix()
        if rel not in ("SHA256SUMS","manifest.json"): expected.append(dict(path=rel,size=p.stat().st_size,sha256=digest(p)))
    if m["files"] != expected: raise ValueError("manifest files differ")
    sums=(d/"SHA256SUMS").read_text().splitlines()
    if sums != [digest(p)+"  "+p.relative_to(d).as_posix() for p in files(d) if p.name!="SHA256SUMS" or p.parent!=d]: raise ValueError("checksum file list differs")
    bundle=d/"checkpoint.bundle"
    subprocess.run(["git","bundle","verify",str(bundle)],check=True)
    heads=git("bundle","list-heads",bundle).splitlines()
    if m["head"] not in [x.split()[0] for x in heads]: raise ValueError("bundle head differs")
    prereqs=[]
    with bundle.open("rb") as f:
        f.readline()
        for line in iter(f.readline,b""):
            if line in (b"\n",b""): break
            if line.startswith(b"-"): prereqs.append(line[1:].split()[0].decode())
    if m["base"] not in prereqs: raise ValueError("bundle prerequisites do not include the manifest base")
    for x in prereqs:
        if subprocess.run(["git","merge-base","--is-ancestor",x,m["base"]]).returncode: raise ValueError("bundle prerequisite "+x+" is not an ancestor of the manifest base")
    with tempfile.TemporaryDirectory() as tmp:
        subprocess.run(["git","init","-q",tmp],check=True)
        objects=git("rev-parse","--path-format=absolute","--git-common-dir")+"/objects"
        alt=pathlib.Path(tmp)/".git/objects/info/alternates"; alt.write_text(objects+"\n")
        subprocess.run(["git","-C",tmp,"bundle","unbundle",str(bundle)],check=True,stdout=subprocess.DEVNULL)
    print("seal verified")
def main():
    a=sys.argv[1:]
    if len(a)==2 and a[0]=="--verify": verify(pathlib.Path(a[1]).resolve()); return
    if len(a) not in (1,2): raise ValueError("usage: seal.sh DIR [BASE] | --verify DIR")
    d=pathlib.Path(a[0]).resolve(); d.mkdir(parents=True,exist_ok=True)
    base=git("rev-parse","--verify",(a[1] if len(a)==2 else "origin/master")+"^{commit}"); head=git("rev-parse","HEAD")
    base=git("merge-base",base,head)  # a moved BASE seals from the fork point
    if base==head: raise ValueError("empty base..HEAD")
    subprocess.run(["git","bundle","create",str(d/"checkpoint.bundle"),base+"..HEAD"],check=True)
    entries=[]
    for p in files(d):
        rel=p.relative_to(d).as_posix()
        if rel not in ("manifest.json","SHA256SUMS"): entries.append(dict(path=rel,size=p.stat().st_size,sha256=digest(p)))
    (d/"manifest.json").write_text(json.dumps(dict(head=head,base=base,files=entries),indent=2)+"\n")
    (d/"SHA256SUMS").write_text("".join(digest(p)+"  "+p.relative_to(d).as_posix()+"\n" for p in files(d) if p.relative_to(d).as_posix()!="SHA256SUMS"))
    verify(d)
try: main()
except (Exception,subprocess.CalledProcessError) as e: print("seal: "+str(e),file=sys.stderr); sys.exit(1)
PY
