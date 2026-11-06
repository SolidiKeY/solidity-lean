#!/usr/bin/env python3
"""Bound one task process tree, with identity-checked cancellation/cleanup.

Uses Linux child-subreaping and the VM's existing cgroup; never systemd-run or
swap changes. The 12 GiB RSS and 4 GiB headroom checks sample every 0.2 seconds;
The existing VM cgroup supplies its hard resident-memory cap. Virtual address
reservations are not capped: Lean's allocator may reserve much more than RSS.
"""
import argparse
import hashlib
import ctypes
import fcntl
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

RESERVE = 4*1024**3
CAP = 12*1024**3
ROOT = Path(__file__).resolve().parents[4]
CGROUP = Path("/sys/fs/cgroup")

CANCEL_SIGNAL = None

def available():
    info = dict(line.split(":",1) for line in Path("/proc/meminfo").read_text().splitlines())
    host = int(info["MemAvailable"].split()[0])*1024
    current = int((CGROUP/"memory.current").read_text())
    limit = (CGROUP/"memory.max").read_text().strip()
    return min(host, host if limit == "max" else int(limit)-current),current

def snapshot():
    rows = {}
    for folder in Path("/proc").iterdir():
        if not folder.name.isdigit(): continue
        try:
            # comm may contain spaces or parentheses; fields after the final
            # closing parenthesis start at field 3. starttime is field 22.
            fields = (folder/"stat").read_text().rsplit(")",1)[1].split()
            status = dict(line.split(":",1) for line in (folder/"status").read_text().splitlines() if ":" in line)
            rows[int(folder.name)] = dict(ppid=int(fields[1]),start=int(fields[19]),state=fields[0],
                rss=int(status.get("VmRSS","0 kB").split()[0])*1024,
                argv=(folder/"cmdline").read_bytes().split(bytes([0])))
        except (FileNotFoundError,ProcessLookupError,PermissionError): pass
    return rows

def collect(rows, remembered, parent):
    # No unrelated concurrent subprocesses are created by this launcher. Linux
    # reparents orphaned grandchildren to this subreaper, not PID 1.
    owned = {pid for pid,start in remembered.items() if pid in rows and rows[pid]["start"] == start}
    owned |= {pid for pid,row in rows.items() if row["ppid"] == os.getpid()}
    while True:
        expanded = owned | {pid for pid,row in rows.items() if row["ppid"] in owned}
        if expanded == owned: break
        owned = expanded
    for pid in owned: remembered[pid]=rows[pid]["start"]
    return {pid for pid in owned if rows[pid]["state"] != "Z"}

def signal_verified(remembered, sig):
    rows = snapshot()
    for pid,start in remembered.items():
        row = rows.get(pid)
        if pid == os.getpid() or row is None or row["start"] != start or row["state"] == "Z": continue
        try:
            descriptor=os.pidfd_open(pid)
            try:
                current=snapshot().get(pid)
                if current is not None and current["start"] == start:
                    signal.pidfd_send_signal(descriptor,sig)
            finally: os.close(descriptor)
        except ProcessLookupError: pass

def reap_adopted(rows, parent):
    for pid,row in rows.items():
        if pid != parent and row["ppid"] == os.getpid() and row["state"] == "Z":
            try: os.waitpid(pid,os.WNOHANG)
            except ChildProcessError: pass

def cleanup(process, remembered):
    # Freeze verified tasks before termination so children cannot escape by
    # spawning during shutdown. Refresh adoption/descendants before each phase.
    for _ in range(3):
        rows=snapshot();collect(rows,remembered,process.pid)
        signal_verified(remembered,signal.SIGSTOP)
    signal_verified(remembered,signal.SIGTERM)
    signal_verified(remembered,signal.SIGCONT)
    deadline=time.monotonic()+5
    while True:
        process.poll()
        rows=snapshot();live=collect(rows,remembered,process.pid)
        reap_adopted(rows,process.pid)
        if not live: break
        if time.monotonic() >= deadline:
            signal_verified(remembered,signal.SIGKILL)
            break
        time.sleep(0.05)
    try: process.wait(timeout=5)
    except subprocess.TimeoutExpired:
        signal_verified(remembered,signal.SIGKILL)
        process.wait(timeout=5)
    for _ in range(20):
        rows=snapshot();live=collect(rows,remembered,process.pid)
        reap_adopted(rows,process.pid)
        if not live: return
        signal_verified(remembered,signal.SIGKILL)
        time.sleep(0.05)
    raise RuntimeError("verified task descendants survived cleanup")

def cancel(signum,frame):
    # Never raise across Popen/state initialization. The protected loop sees
    # this flag and always reaches finally cleanup, even for spawn-time signals.
    global CANCEL_SIGNAL
    CANCEL_SIGNAL = signum

parser = argparse.ArgumentParser()
parser.add_argument("--receipt",type=Path,required=True)
parser.add_argument("--timeout",type=float,default=900)
parser.add_argument("--output",type=Path)
parser.add_argument("command",nargs=argparse.REMAINDER)
args = parser.parse_args()
command = args.command[1:] if args.command[:1] == ["--"] else args.command
assert command
assert not args.receipt.resolve().is_relative_to(ROOT), "H44 resource evidence must stay outside git"
args.receipt.unlink(missing_ok=True)
if args.output:
    args.output=args.output.resolve()
    assert not args.output.is_relative_to(ROOT), "H44 proof output must stay outside git"
    assert args.output != args.receipt.resolve()
    args.output.parent.mkdir(parents=True,exist_ok=True)
lock = Path("/tmp/solidity-lean-feature-groups-20261025/writer.lock")
lock.parent.mkdir(parents=True,exist_ok=True)
with lock.open("a") as stream:
    fcntl.flock(stream,fcntl.LOCK_EX|fcntl.LOCK_NB)
    changed = subprocess.check_output(["git","diff","--name-only","HEAD"],cwd=ROOT,text=True).splitlines()
    assert all(p.startswith(("tests/h62/item2/audit-abi-world/","scripts/h62/item2/audit-abi-world/")) or p == "docs/feature-work/h62-2-audit-abi-world.md" for p in changed), changed
    assert len(Path("/proc/swaps").read_text().splitlines()) == 1, "active swap is prohibited"
    space,current = available()
    assert space >= RESERVE, "initial 4 GiB reserve unavailable"
    # PR_SET_CHILD_SUBREAPER. Fail closed if this Linux facility is unavailable.
    assert ctypes.CDLL(None,use_errno=True).prctl(36,1,0,0,0) == 0
    signal.signal(signal.SIGTERM,cancel);signal.signal(signal.SIGINT,cancel)
    env = dict(os.environ,LEAN_NUM_THREADS="1",LEAN_LSP_MAX_OPEN_FILES="1")
    started = time.monotonic()
    output_stream=args.output.open("wb") if args.output else None
    process = subprocess.Popen(command,cwd=ROOT,env=env,start_new_session=True,stdout=output_stream)
    remembered = {}
    peak_rss,peak_cgroup,min_space = 0,current,space
    max_compilers,max_workers,max_jobs = 0,0,0
    swap_seen=False;reason=None
    try:
        while True:
            rows=snapshot();live=collect(rows,remembered,process.pid)
            code=process.poll()
            if code is not None: live.discard(process.pid)
            reap_adopted(rows,process.pid)
            rss=sum(rows[p]["rss"] for p in live)
            compilers=0;workers=0
            for pid in live:
                row=rows[pid];argv=row["argv"]
                if not argv or not argv[0].endswith(b"/lean") or b"--server" in argv: continue
                if b"--worker" in argv:
                    workers += row["rss"] > 512*1024**2
                elif any(a.endswith(b".lean") for a in argv): compilers += 1
            space,current=available()
            peak_rss=max(peak_rss,rss);peak_cgroup=max(peak_cgroup,current);min_space=min(min_space,space)
            max_compilers=max(max_compilers,compilers);max_workers=max(max_workers,workers);max_jobs=max(max_jobs,compilers+workers)
            swap_seen |= len(Path("/proc/swaps").read_text().splitlines()) != 1
            if CANCEL_SIGNAL is not None: reason="cancelled"
            elif space < RESERVE: reason="4 GiB reserve crossed"
            elif rss > CAP: reason="12 GiB aggregate task RSS cap crossed"
            elif compilers+workers > 1: reason="parallel heavy Lean jobs detected"
            elif time.monotonic()-started > args.timeout: reason="bounded timeout"
            elif swap_seen: reason="active swap appeared"
            elif code is not None and live: reason="launcher exited with live descendants"
            if reason or code is not None: break
            time.sleep(0.2)
    except BaseException as error:
        reason="guard exception: "+repr(error)
    finally:
        # Ignore repeated catchable cancellation while cleaning verified tasks.
        signal.signal(signal.SIGTERM,signal.SIG_IGN);signal.signal(signal.SIGINT,signal.SIG_IGN)
        try:
            cleanup(process,remembered)
        finally:
            if output_stream: output_stream.close()
    code=process.returncode
    report=dict(command=command,exit_code=code,reason=reason,elapsed_seconds=time.monotonic()-started,
        peak_task_rss_bytes=peak_rss,peak_cgroup_current_bytes=peak_cgroup,minimum_available_bytes=min_space,
        max_compiler_processes=max_compilers,max_heavy_workers=max_workers,max_heavy_lean_jobs=max_jobs,
        reserve_bytes=RESERVE,task_cap_bytes=CAP,swap_active_seen=swap_seen,subreaper=True,
        cleanup_complete=True,sample_interval_seconds=0.2,lean_num_threads=1,
        guard_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        hard_cgroup_limit_bytes=int((CGROUP/"memory.max").read_text()),
        address_space_limit=None,
        stdout_file=str(args.output) if args.output else None,
        stdout_sha256=hashlib.sha256(args.output.read_bytes()).hexdigest() if args.output else None)
    args.receipt.parent.mkdir(parents=True,exist_ok=True)
    args.receipt.write_text(json.dumps(report,indent=2)+"\n")
    raise SystemExit(code if not reason and code >= 0 else 1)
