#!/usr/bin/env python3
"""Advise only clean generated build pages away; preserve files and all limits.

Run between bounded jobs. No global cache drop or source/toolchain advice.
POSIX_FADV_DONTNEED ignores dirty pages. Matched timings need the same policy.
"""
import fcntl,json,os,stat,hashlib
from pathlib import Path
root=Path(__file__).resolve().parents[4]
build=root/".lake/build"
def memory():
    return {name:(Path("/sys/fs/cgroup")/name).read_text() for name in
            ("memory.current","memory.stat","memory.events","memory.max","memory.swap.current")}
with open("/tmp/solidity-lean-feature-groups-20261025/writer.lock","a") as lock:
    fcntl.flock(lock,fcntl.LOCK_EX)
    for process in Path("/proc").iterdir():
        if process.name.isdigit():
            try:
                name=(process/"comm").read_text().strip()
                state=(process/"stat").read_text().rsplit(")",1)[1].split()[0]
            except (FileNotFoundError,PermissionError,ProcessLookupError): continue
            assert state == "Z" or name not in ("lean","lake"), "Lean/Lake still active"
    for folder in (root/".lake",build):
        assert folder.is_dir() and not folder.is_symlink(), "symlinked/missing cache root"
    assert build.resolve() == root/".lake/build", "cache root escaped checkout"
    before=memory();entries=[];errors=[]
    for directory,dirs,files in os.walk(build,followlinks=False):
        dirs[:]=sorted(d for d in dirs if not (Path(directory)/d).is_symlink())
        for name in sorted(files):
            path=Path(directory)/name
            try:
                fd=os.open(path,os.O_RDONLY|os.O_NOFOLLOW)
                try:
                    item=os.fstat(fd)
                    if not stat.S_ISREG(item.st_mode): continue
                    os.posix_fadvise(fd,0,0,os.POSIX_FADV_DONTNEED)
                    entries.append([str(path.relative_to(root)),item.st_size,item.st_mtime_ns])
                finally: os.close(fd)
            except OSError as error: errors.append([str(path),str(error)])
    print(json.dumps(dict(policy="generated-build-only-readonly-nofollow-DONTNEED",before=before,after=memory(),
        files=len(entries),bytes=sum(row[1] for row in entries),entries_sha256=hashlib.sha256(json.dumps(entries).encode()).hexdigest(),errors=errors),indent=2))
    assert not errors
