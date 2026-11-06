#!/usr/bin/env python3
"""Release only specified regular-file cache pages; never deletes or modifies bytes."""
import os, stat
from pathlib import Path

def memory_snapshot():
    group=Path("/sys/fs/cgroup")
    stats={k:int(v) for k,v in (row.split() for row in (group/"memory.stat").read_text().splitlines())}
    return dict(current=int((group/"memory.current").read_text()),maximum=int((group/"memory.max").read_text()),
        **{k:stats[k] for k in ["anon","file","file_dirty","inactive_file","active_file","slab_reclaimable"]})

def advise_roots(roots):
    if not hasattr(os,"posix_fadvise"):raise RuntimeError("POSIX file-cache advice unavailable")
    before=memory_snapshot();count=0;size=0;seen=set()
    for root in roots:
        root=Path(root)
        if root.is_symlink():raise RuntimeError("Cache root must not be a symlink")
        paths=[root] if root.is_file() else root.rglob("*")
        for path in paths:
            if path in seen:continue
            seen.add(path)
            info=path.lstat()
            if not stat.S_ISREG(info.st_mode):continue
            fd=os.open(path,os.O_RDONLY|os.O_NOFOLLOW)
            try:os.posix_fadvise(fd,0,0,os.POSIX_FADV_DONTNEED)
            finally:os.close(fd)
            count+=1;size+=info.st_size
    return dict(roots=[str(Path(p)) for p in roots],operation="POSIX_FADV_DONTNEED on regular read-only files; no deletion/content write",files=count,bytes=size,before=before,after=memory_snapshot())
