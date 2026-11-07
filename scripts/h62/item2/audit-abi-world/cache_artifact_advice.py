#!/usr/bin/env python3
"""Read-only clean-page advice for this VM's discovered local Lake cache.

No network/cache fetch, removal, content write, global drop or limit change.
Run between bounded jobs under the shared writer lock. Only current-UID regular
artifact files are eligible; dirty pages are ignored by POSIX_FADV_DONTNEED.
The byte count is advice, not a guarantee of eviction.
"""
import fcntl,hashlib,json,os,stat
from pathlib import Path
cache=Path.home()/".cache/lake/artifacts"
def memory():
 return {name:(Path("/sys/fs/cgroup")/name).read_text() for name in
         ("memory.current","memory.stat","memory.events","memory.max","memory.swap.current")}
with open("/tmp/solidity-lean-feature-groups-20261025/writer.lock","a") as lock:
 fcntl.flock(lock,fcntl.LOCK_EX)
 for process in Path("/proc").iterdir():
  if not process.name.isdigit():continue
  try:
   name=(process/"comm").read_text().strip()
   state=(process/"stat").read_text().rsplit(")",1)[1].split()[0]
  except (FileNotFoundError,PermissionError,ProcessLookupError):continue
  assert state=="Z" or name not in ("lean","lake"),"Lean/Lake still active"
 for path in (Path.home(),cache.parent.parent,cache.parent,cache):
  assert path.is_dir() and not path.is_symlink(),"symlinked/missing artifact root"
 assert cache.resolve()==cache,"artifact root escaped canonical location"
 before=memory();entries=[];errors=[];skipped=[]
 anchor=os.open(cache,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW)
 try:
  for directory,dirs,files,parent in os.fwalk(".",dir_fd=anchor,follow_symlinks=False):
   dirs.sort()
   for name in sorted(files):
    fd=None
    try:
     fd=os.open(name,os.O_RDONLY|os.O_NOFOLLOW|os.O_NONBLOCK,dir_fd=parent);info=os.fstat(fd)
     if not stat.S_ISREG(info.st_mode) or info.st_uid!=os.geteuid():
      skipped.append(str(Path(directory)/name));continue
     os.posix_fadvise(fd,0,0,os.POSIX_FADV_DONTNEED)
     entries.append([str(Path(directory)/name),info.st_size,info.st_mtime_ns])
    except OSError as error:errors.append([str(Path(directory)/name),str(error)])
    finally:
     if fd is not None:os.close(fd)
 finally:os.close(anchor)
 print(json.dumps(dict(policy="local-Lake-artifacts-current-UID-readonly-anchored-nofollow-DONTNEED",root=str(cache),before=before,after=memory(),files=len(entries),bytes=sum(x[1] for x in entries),entries_sha256=hashlib.sha256(json.dumps(entries).encode()).hexdigest(),skipped=skipped,errors=errors),indent=2))
 assert not errors
