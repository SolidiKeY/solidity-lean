#!/usr/bin/env bash
set -euo pipefail
exec python3 - "$@" <<'PY'
import os,pathlib,shutil,subprocess,sys,tempfile

def run(*args,**kw): return subprocess.run(args,stdout=subprocess.PIPE,stderr=subprocess.DEVNULL,text=True,**kw)
def main():
    args=sys.argv[1:]
    if args not in ([],["--free"]): raise ValueError("usage: disk.sh [--free]")
    repo=pathlib.Path(os.environ.get("DISK_REPO",os.getcwd())).resolve(); cg=pathlib.Path(os.environ.get("DISK_CGROUP","/sys/fs/cgroup"))
    free=shutil.disk_usage(repo).free; print(f"disk: path={repo} free={free}")
    print(f"ram: current={(cg/"memory.current").read_text().strip()} max={(cg/"memory.max").read_text().strip()}")
    if not args and free>=int(os.environ.get("DISK_MIN_FREE_BYTES","2147483648")): return
    for tool in ("docker","podman"):
        if not shutil.which(tool): continue
        p=run(tool,"ps","-aq","--filter","status=exited")
        if p.returncode==0:
            for ident in p.stdout.splitlines():
                if ident and run(tool,"rm",ident).returncode==0: print(f"deleted: {tool}:{ident}")
    p=run("git","-C",str(repo),"worktree","list","--porcelain")
    if p.returncode: raise ValueError("cannot list worktrees")
    worktrees=[line[9:] for line in p.stdout.splitlines() if line.startswith("worktree ")]
    for wt in worktrees[1:]:
        build=pathlib.Path(wt)/".lake/build"
        if build.is_dir() and not build.is_symlink(): shutil.rmtree(build); print(f"deleted: {build}")
    common=run("git","-C",str(repo),"rev-parse","--path-format=absolute","--git-common-dir").stdout.strip(); objects=str(pathlib.Path(common)/"objects")
    def valid(d):
        if not d.is_dir() or d.is_symlink() or not (d/"SHA256SUMS").is_file(): return False
        if any(p.name==".git" for p in d.rglob(".git")): return False
        if run("git","-C",str(d),"rev-parse","--is-inside-work-tree").returncode==0: return False
        if run("sha256sum","-c","--strict","SHA256SUMS",cwd=d).returncode: return False
        bundles=list(d.rglob("*.bundle"))
        if not bundles: return False
        for b in bundles:
            if run("git","-C",str(repo),"bundle","verify",str(b)).returncode: return False
            with tempfile.TemporaryDirectory() as tmp:
                if run("git","init","-q",tmp).returncode: return False
                (pathlib.Path(tmp)/".git/objects/info/alternates").write_text(objects+"\n")
                if run("git","-C",tmp,"bundle","unbundle",str(b)).returncode: return False
        return True
    seals=[]
    for root in os.environ.get("DISK_EVIDENCE_ROOTS","/workspace").split(":"):
        p=pathlib.Path(root)
        if p.is_dir():
            for d in p.iterdir():
                if valid(d): seals.append((d.joinpath("SHA256SUMS").stat().st_mtime_ns,d))
    if seals:
        newest=max(t for t,_ in seals)
        for t,d in seals:
            if t<newest: shutil.rmtree(d); print(f"deleted: {d}")
try: main()
except Exception as e: print("disk: "+str(e),file=sys.stderr); sys.exit(1)
PY
