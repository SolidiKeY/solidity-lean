#!/usr/bin/env python3
"""Advisory eviction of explicitly listed owned toolchain/cache inputs only.

No system-wide drop_caches or file modification. DONTNEED is advisory; record
before/after cgroup charge instead of claiming guaranteed physical coldness.
"""
import argparse,json,os,pathlib,time
p=argparse.ArgumentParser();p.add_argument("--roots",type=pathlib.Path,required=True);p.add_argument("--output",type=pathlib.Path,required=True);a=p.parse_args()
roots=[pathlib.Path(x) for x in json.loads(a.roots.read_text())]
assert all(x.is_absolute() for x in roots)
roots=[x.resolve() for x in roots]
# This operational helper intentionally accepts only this task's owned workspace.
allowed=[pathlib.Path(x) for x in ("/workspace/.setup/tools","/workspace/h62-toolchains","/workspace/h62-migrate-examples-evidence","/workspace/solidity-lean-migrate-examples/.lake")]
assert all(any(x.is_relative_to(base) for base in allowed) for x in roots)
assert all(x.exists() for x in roots),"cache preparation root missing"
start=time.monotonic();before=int(pathlib.Path("/sys/fs/cgroup/memory.current").read_text());count=0;size=0;errors=[]
for root in roots:
    paths=[root] if root.is_file() else (path for base,dirs,files in os.walk(root,followlinks=False) for path in (pathlib.Path(base)/name for name in files))
    for path in paths:
        if path.is_symlink() or not path.is_file():continue
        try:
            fd=os.open(path,os.O_RDONLY|os.O_NOFOLLOW)
            try:os.posix_fadvise(fd,0,0,os.POSIX_FADV_DONTNEED);size+=os.fstat(fd).st_size;count+=1
            finally:os.close(fd)
        except OSError as exc:errors.append({"path":str(path),"error":str(exc)})
result={"roots":[str(x) for x in roots],"files_advised":count,"bytes_advised":size,"cgroup_current_before":before,"cgroup_current_after":int(pathlib.Path("/sys/fs/cgroup/memory.current").read_text()),"seconds":time.monotonic()-start,"errors":errors,"boundary":"advisory only; excludes symlinked files/directories; no guarantee of full eviction"}
a.output.write_text(json.dumps(result,indent=2)+"\n");print(json.dumps(result));raise SystemExit(1 if errors else 0)
