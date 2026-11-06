"""Sampled availability-after-reclaim estimate; not an allocation guarantee."""
from pathlib import Path
import os

def availability(cap, current, file, inactive, dirty, writeback, host_available, shmem=0, unevictable=0, host_low=0):
    values=[cap,current,file,inactive,dirty,writeback,host_available,shmem,unevictable,host_low]
    if any(not isinstance(v,int) or v<0 for v in values) or cap==0:
        raise ValueError("invalid resource counters")
    inactive_reclaimable=max(0,min(inactive,file)-dirty-writeback)
    inactive_available=min(host_available,cap,max(0,cap-current+inactive_reclaimable))
    clean_file=max(0,file-shmem-dirty-writeback-unevictable)
    # Kernel-style page-cache safety deduction. Slab reclaim is never counted.
    cache_allowance=min(clean_file//2,host_low)
    reclaimable=clean_file-cache_allowance
    raw=max(0,cap-current)
    cg_available=min(cap,max(0,cap-current+reclaimable))
    return dict(cap_bytes=cap,current_bytes=current,raw_headroom_bytes=raw,
                file_bytes=file,inactive_file_bytes=inactive,dirty_bytes=dirty,
                writeback_bytes=writeback,reclaimable_estimate_bytes=reclaimable,
                host_available_bytes=host_available,shmem_bytes=shmem,unevictable_bytes=unevictable,
                host_low_watermark_bytes=host_low,clean_file_estimate_bytes=clean_file,
                cache_allowance_bytes=cache_allowance,
                inactive_only_estimate_bytes=inactive_available,
                available_estimate_bytes=min(host_available,cg_available))

def snapshot(cgroup=Path("/sys/fs/cgroup"),meminfo=Path("/proc/meminfo"),zoneinfo=Path("/proc/zoneinfo")):
    stats={line.split()[0]:int(line.split()[1]) for line in (cgroup/"memory.stat").read_text().splitlines()}
    host={line.split()[0].rstrip(":"):int(line.split()[1])*1024 for line in meminfo.read_text().splitlines() if len(line.split())>=2 and line.split()[1].isdigit()}
    low_pages=sum(int(line.split()[1]) for line in zoneinfo.read_text().splitlines() if line.split() and line.split()[0]=='low')
    low_bytes=low_pages*os.sysconf('SC_PAGE_SIZE')
    # The selected VM hard cap is at this cgroup mount root. Ancestors above
    # the mount are not visible. Do not substitute host availability alone.
    return availability(int((cgroup/"memory.max").read_text()),
                        int((cgroup/"memory.current").read_text()),
                        stats["file"],stats["inactive_file"],stats["file_dirty"],
                        stats["file_writeback"],host["MemAvailable"],stats["shmem"],stats["unevictable"],low_bytes)
