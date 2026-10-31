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
