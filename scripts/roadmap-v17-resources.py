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

def resource_snapshot():
    if Path('/proc/self/cgroup').read_text().strip()!='0::/':
        raise ValueError('unsupported enclosing cgroup layout')
    matches=re.findall(r'^MemAvailable:\s+([0-9]+) kB$',Path('/proc/meminfo').read_text(),re.M)
    if len(matches)!=1: raise ValueError('malformed host availability')
    def measured(path):
        raw=Path(path).read_text().strip()
        if not re.fullmatch(r'0|[1-9][0-9]*',raw): raise ValueError('malformed/unlimited cgroup measurement')
        return int(raw)
    host=int(matches[0])*1024
    limit=measured('/sys/fs/cgroup/memory.max'); used=measured('/sys/fs/cgroup/memory.current')
    r=dict(hostMemAvailableBytes=host,enclosingCgroupLimitBytes=limit,enclosingCgroupCurrentBytes=used,headroomBytes=min(host,limit-used))
    check_headroom(r)
    return r
