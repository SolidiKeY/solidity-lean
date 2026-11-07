#!/usr/bin/env python3
"""Run only this job's process group, serial Lean, 12 GiB cap/4 GiB reserve.
RLIMIT_AS is per-process; aggregate RSS is sampled. No systemd or swap. Logs and JSON evidence must be outside the checkout.
"""
import argparse
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import time

GIB = 1024 ** 3

def available():
    rows = dict(line.split(":", 1) for line in Path("/proc/meminfo").read_text().splitlines())
    host = int(rows["MemAvailable"].split()[0]) * 1024
    limit = Path("/sys/fs/cgroup/memory.max").read_text().strip()
    if limit == "max": return host
    current = int(Path("/sys/fs/cgroup/memory.current").read_text())
    return min(host, int(limit)-current)

def members(group):
    result = []
    for p in Path("/proc").glob("[0-9]*"):
        try:
            raw = (p/"stat").read_text()
            fields = raw[raw.rfind(")")+2:].split()
            if int(fields[2]) != group or fields[0] == "Z": continue
            rss = int(fields[21]) * os.sysconf("SC_PAGE_SIZE")
            cmd = (p/"cmdline").read_bytes().replace(b"\0", b" ").decode(errors="replace")
            result.append((int(p.name), rss, cmd))
        except (FileNotFoundError, ProcessLookupError, PermissionError): pass
    return result

def terminate_group(group):
    for sig in (signal.SIGTERM, signal.SIGKILL):
        if members(group):
            try: os.killpg(group, sig)
            except ProcessLookupError: pass
        deadline = time.monotonic() + 5
        while members(group) and time.monotonic() < deadline:
            time.sleep(0.1)
    return not members(group)

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--cwd", type=Path, required=True)
    ap.add_argument("--toolchain", type=Path, required=True)
    ap.add_argument("--log", type=Path, required=True)
    ap.add_argument("--result", type=Path, required=True)
    ap.add_argument("command", nargs=argparse.REMAINDER)
    args = ap.parse_args()
    cmd = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not cmd: raise SystemExit("missing command")
    if len(Path("/proc/swaps").read_text().splitlines()) > 1:
        raise SystemExit("swap enabled: refusing heavy work")
    if available() < 4 * GIB: raise SystemExit("less than 4 GiB available reserve")
    env = dict(os.environ, LEAN_NUM_THREADS="1", XDG_CACHE_HOME="/workspace/h62-generic-yul-views/cache-v435")
    env["PATH"] = str(args.toolchain/"bin") + ":" + env["PATH"]
    def limits(): resource.setrlimit(resource.RLIMIT_AS, (12*GIB, 12*GIB))
    started = time.monotonic()
    peak, reason, max_lean = 0, None, 0
    seen = {}
    with args.log.open("w") as log:
        proc = subprocess.Popen(cmd, cwd=args.cwd, env=env, stdout=log, stderr=subprocess.STDOUT,
            start_new_session=True, preexec_fn=limits)
        try:
            while proc.poll() is None:
                group = members(proc.pid)
                peak = max(peak, sum(rss for _,rss,_ in group))
                now = time.monotonic()
                lean_count = sum("/bin/lean " in command for _,_,command in group)
                max_lean = max(max_lean, lean_count)
                if lean_count > 1: reason = "multiple simultaneous Lean processes refused"
                for pid, rss, command in group:
                    seen.setdefault(pid, (now, command))
                    if "/bin/lean " in command and now-seen[pid][0] > 300:
                        reason = "module exceeded 300 second resource gate"
                if peak > 12*GIB: reason = "aggregate RSS exceeded 12 GiB"
                if available() < 4*GIB: reason = "available memory below 4 GiB reserve"
                if reason:
                    terminate_group(proc.pid)
                    break
                time.sleep(0.2)
        finally:
            if members(proc.pid):
                reason = reason or "launcher exited with live descendants"
            quiescent = terminate_group(proc.pid)
            if not quiescent: reason = "owned process group failed to quiesce"
        code = proc.wait()
    result = dict(command=cmd,cwd=str(args.cwd),exit=code,resource_stop=reason,process_group_id=proc.pid,
        wall_seconds=time.monotonic()-started,peak_aggregate_rss_bytes=peak,
        lean_threads=1,max_simultaneous_lean=max_lean,process_group_quiescent=quiescent,
        per_process_virtual_limit_bytes=12*GIB,sampled_aggregate_limit_bytes=12*GIB,reserve_bytes=4*GIB,
        log=str(args.log),observed_processes={str(k):v[1] for k,v in seen.items()})
    args.result.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({k:v for k,v in result.items() if k!="observed_processes"},indent=2))
    raise SystemExit(1 if reason else code)

if __name__ == "__main__": main()
