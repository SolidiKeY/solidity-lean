"""Linux helpers restricted to process groups created by this task's runners."""
import os, signal, time
from pathlib import Path

def members(group):
    found=[]
    for proc in Path("/proc").glob("[0-9]*"):
        try:
            stat=(proc/"stat").read_text().rsplit(")",1)[1].split()
            if int(stat[2])==group and stat[0]!="Z":
                found.append((int(proc.name),int(stat[21])*os.sysconf("SC_PAGE_SIZE")))
        except (OSError,ValueError,IndexError): pass
    return found

def stop_owned(group,root):
    if group<=1 or group==os.getpgrp(): raise RuntimeError("unsafe process group")
    root=Path(root).resolve()
    for sig in (signal.SIGTERM,signal.SIGKILL):
        active=members(group)
        if not active: return
        for pid,_ in active:
            try: cwd=Path(f"/proc/{pid}/cwd").resolve(strict=True)
            except FileNotFoundError: continue
            if not cwd.is_relative_to(root): raise RuntimeError(f"unexpected cwd for owned group member {pid}")
        try: os.killpg(group,sig)
        except ProcessLookupError: return
        deadline=time.monotonic()+10
        while members(group) and time.monotonic()<deadline: time.sleep(0.1)
    if members(group): raise RuntimeError("owned process group survived SIGKILL")
