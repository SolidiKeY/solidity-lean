"""Fail-closed resource measurements shared by V17 build and kernel consumers."""
from pathlib import Path
import re
CAP = 12 * 1024**3
RESERVE = 2 * 1024**3

def check_headroom(r):
    keys=('hostMemAvailableBytes','enclosingCgroupLimitBytes','enclosingCgroupCurrentBytes','headroomBytes')
    if not all(k in r and type(r[k]) is int and r[k]>=0 for k in keys):
        raise ValueError('invalid/missing enclosing memory measurements')
    host,limit,used,available=(r[k] for k in keys)
    if used>limit or available!=min(host,limit-used) or available<CAP+RESERVE:
        raise ValueError('insufficient effective headroom/OS reserve')

class ResourceObservationError(ValueError):
    """A refusal with only telemetry actually obtained before it failed."""
    def __init__(self,message,observations):
        super().__init__(message)
        self.observations=observations


def resource_snapshot():
    observations={'raw':{},'measurements':{}}
    def read(path):
        value=Path(path).read_text().strip(); observations['raw'][path]=value; return value
    try:
        if read('/proc/self/cgroup')!='0::/':
            raise ValueError('unsupported enclosing cgroup layout')
        matches=re.findall(r'^MemAvailable:\s+([0-9]+) kB$',read('/proc/meminfo'),re.M)
        if len(matches)!=1: raise ValueError('malformed host availability')
        host=int(matches[0])*1024; observations['measurements']['hostMemAvailableBytes']=host
        def measured(path,key):
            raw=read(path)
            if not re.fullmatch(r'0|[1-9][0-9]*',raw): raise ValueError('malformed/unlimited cgroup measurement')
            value=int(raw); observations['measurements'][key]=value; return value
        limit=measured('/sys/fs/cgroup/memory.max','enclosingCgroupLimitBytes')
        used=measured('/sys/fs/cgroup/memory.current','enclosingCgroupCurrentBytes')
        r=dict(hostMemAvailableBytes=host,enclosingCgroupLimitBytes=limit,enclosingCgroupCurrentBytes=used,headroomBytes=min(host,limit-used))
        observations['measurements']=r
        check_headroom(r)
        return r
    except (OSError,ValueError) as error:
        raise ResourceObservationError(str(error),observations) from error



def hash_file(path):
    """Read-only direct IO avoids repopulating file cache during inventories.

    Unsupported filesystems fall back to ordinary reads; the unchanged resource
    guard still measures actual capacity afterward. No cache pages are dropped.
    """
    import errno,hashlib,mmap,os
    before=path.stat()
    result=None
    if before.st_size and hasattr(os,'O_DIRECT'):
        fd=None;buffer=None
        try:
            fd=os.open(path,os.O_RDONLY|os.O_DIRECT)
            buffer=mmap.mmap(-1,1024*1024);h=hashlib.sha256();total=0
            while total<before.st_size:
                n=os.readv(fd,[buffer])
                if not n:raise ValueError('input changed during direct checksum')
                h.update(memoryview(buffer)[:n]);total+=n
            if total!=before.st_size:raise ValueError('input changed during direct checksum')
            result=h.hexdigest()
        except OSError as error:
            if error.errno not in (errno.EINVAL,errno.EOPNOTSUPP,errno.ENOSYS):raise
        finally:
            if buffer is not None:buffer.close()
            if fd is not None:os.close(fd)
    if result is None:
        with path.open('rb') as stream:result=hashlib.file_digest(stream,'sha256').hexdigest()
    after=path.stat()
    if (before.st_dev,before.st_ino,before.st_size,before.st_mtime_ns,before.st_ctime_ns)!=(after.st_dev,after.st_ino,after.st_size,after.st_mtime_ns,after.st_ctime_ns):
        raise ValueError('input changed during checksum')
    return result

def tool_inputs(current):
    """Hash installed elaboration/evaluation inputs; do not rebuild or copy them."""
    import hashlib
    prefix=Path(current['runtime']['lean']['path']).parent.parent
    files={}
    for path in sorted((prefix/'lib').rglob('*')):
        if path.is_file() and ('.olean' in path.name or '.so' in path.name):
            files[str(path.resolve())]=hash_file(path)
    if not files:raise ValueError('missing installed toolchain import inputs')
    return files
