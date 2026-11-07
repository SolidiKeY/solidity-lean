"""Conservative available memory: credit only clean, unmapped file cache."""
from pathlib import Path

def cgroup_available(cap,current,stat):
    # Never credit anonymous, mapped, dirty/writeback, shared or unevictable pages.
    file_lru=min(stat.get("file",0),stat.get("inactive_file",0)+stat.get("active_file",0))
    protected=sum(stat.get(k,0) for k in ("file_mapped","file_dirty","file_writeback","shmem","unevictable"))
    reclaimable=min(current,max(0,file_lru-protected))
    return max(0,min(cap,cap-current+reclaimable)),reclaimable

def snapshot(cg=Path("/sys/fs/cgroup")):
    cap=int((cg/"memory.max").read_text()); before=int((cg/"memory.current").read_text())
    stat={k:int(v) for k,v in (line.split() for line in (cg/"memory.stat").read_text().splitlines())}
    current=max(before,int((cg/"memory.current").read_text()))
    available,reclaimable=cgroup_available(cap,current,stat)
    host=int(next(x.split()[1] for x in Path("/proc/meminfo").read_text().splitlines() if x.startswith("MemAvailable:")))*1024
    return {"cap_bytes":cap,"charged_bytes":current,"clean_unmapped_file_cache_bytes":reclaimable,"cgroup_available_bytes":available,"host_available_bytes":host,"swap_bytes":int((cg/"memory.swap.current").read_text()),"memory_stat":stat}

def stop_reason(sample,reserve):
    if sample["swap_bytes"]: return "swap detected"
    if sample["host_available_bytes"]<reserve: return "4GiB host available reserve"
    if sample["cgroup_available_bytes"]<reserve: return "4GiB cgroup available reserve"
    return None
