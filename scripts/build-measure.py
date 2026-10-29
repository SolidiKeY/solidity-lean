#!/usr/bin/env python3
"""Run a build command while sampling /proc; report per-module time and RSS.

Usage: scripts/build-measure.py --out DIR [--interval S] -- CMD [ARGS...]

The command runs in its own process group. Every interval the watcher reads,
for each `lean`/`lake` process in that group, `VmRSS` and `VmHWM` from
`/proc/<pid>/status`, and `MemAvailable` from `/proc/meminfo`. A `lean`
process is attributed to the first `.lean` path in its command line; its
first and last sightings bound its elapsed time (resolution: one interval),
and its last `VmHWM` is its peak resident set. Writes to DIR:

- `samples.csv`: time, MemAvailable, aggregate lean RSS, live lean workers;
- `modules.csv`: one row per lean process (module, start, end, elapsed,
  peak RSS), sorted by start;
- `oleans.csv`: modification time of each `.olean` under every
  `.lake/build/lib/lean` reachable from the working directory, after the run;
- `summary.json`: command, exit status, wall time, minimum MemAvailable,
  peak aggregate lean RSS, peak concurrent workers and the kernel log lines
  reporting an OOM kill during the run.

Only the standard library is used. The watcher never kills anything. A
killed command exits 137; a killed `lean` worker makes Lake fail the module
instead, so the kernel log (`dmesg`) is checked as well.
"""
import argparse
import csv
import json
import os
import signal
import subprocess
import sys
import time


def read_status(pid):
    vals = {}
    try:
        with open(f"/proc/{pid}/status") as f:
            for line in f:
                key, _, rest = line.partition(":")
                if key in ("Name", "VmRSS", "VmHWM", "PPid"):
                    vals[key] = rest.strip()
    except OSError:
        return None
    return vals


def kib(s):
    return int(s.split()[0]) if s else 0


def mem_available_kib():
    with open("/proc/meminfo") as f:
        for line in f:
            if line.startswith("MemAvailable:"):
                return kib(line.split(":", 1)[1])
    return 0


def pgid_of(pid):
    try:
        with open(f"/proc/{pid}/stat") as f:
            fields = f.read().rsplit(")", 1)[1].split()
        return int(fields[2])
    except (OSError, IndexError, ValueError):
        return None


def cmdline(pid):
    try:
        with open(f"/proc/{pid}/cmdline", "rb") as f:
            return [a.decode(errors="replace") for a in f.read().split(b"\0") if a]
    except OSError:
        return []


def module_of(args, cwd):
    for a in args[1:]:
        if a.endswith(".lean"):
            return os.path.relpath(os.path.join(cwd, a), os.getcwd()) if cwd else a
    return " ".join(args[1:3])


def proc_cwd(pid):
    try:
        return os.readlink(f"/proc/{pid}/cwd")
    except OSError:
        return None


def scan_oleans(root):
    rows = []
    for dirpath, dirnames, filenames in os.walk(root):
        if dirpath.endswith(os.path.join(".lake", "build", "lib", "lean")):
            for d2, _, fs in os.walk(dirpath):
                for fn in fs:
                    if fn.endswith(".olean"):
                        p = os.path.join(d2, fn)
                        st = os.stat(p)
                        rows.append((os.path.relpath(p, root), st.st_mtime, st.st_size))
            dirnames[:] = []
        # Do not descend into toolchains or VCS metadata.
        dirnames[:] = [d for d in dirnames if d not in (".git", "node_modules")]
    return rows


def kernel_oom_lines():
    try:
        out = subprocess.run(["dmesg"], capture_output=True, text=True).stdout
    except OSError:
        return []
    return [l for l in out.splitlines() if "Out of memory" in l or "oom-kill" in l]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--interval", type=float, default=0.5)
    ap.add_argument("cmd", nargs=argparse.REMAINDER)
    ns = ap.parse_args()
    cmd = ns.cmd[1:] if ns.cmd and ns.cmd[0] == "--" else ns.cmd
    if not cmd:
        ap.error("missing command")
    os.makedirs(ns.out, exist_ok=True)

    dmesg_before = kernel_oom_lines()
    t0 = time.time()
    child = subprocess.Popen(cmd, start_new_session=True)
    group = child.pid
    procs = {}  # pid -> dict(module, start, end, hwm, name)
    min_avail = mem_available_kib()
    peak_agg = (0, 0.0)
    peak_workers = 0
    samples = open(os.path.join(ns.out, "samples.csv"), "w", newline="")
    sw = csv.writer(samples)
    sw.writerow(["t", "mem_available_kib", "lean_rss_kib", "lean_workers", "lake_rss_kib"])
    status = None
    while status is None:
        now = time.time() - t0
        agg = lake_rss = workers = 0
        for entry in os.listdir("/proc"):
            if not entry.isdigit():
                continue
            pid = int(entry)
            if pgid_of(pid) != group:
                continue
            st = read_status(pid)
            if not st or st.get("Name") not in ("lean", "lake"):
                continue
            rss = kib(st.get("VmRSS", ""))
            rec = procs.get(pid)
            if rec is None:
                args = cmdline(pid)
                rec = procs[pid] = {
                    "name": st["Name"],
                    "module": module_of(args, proc_cwd(pid)) if st["Name"] == "lean" else "lake",
                    "start": now,
                    "end": now,
                    "hwm": 0,
                }
            rec["end"] = now
            rec["hwm"] = max(rec["hwm"], kib(st.get("VmHWM", "")), rss)
            if st["Name"] == "lean":
                agg += rss
                workers += 1
            else:
                lake_rss += rss
        avail = mem_available_kib()
        min_avail = min(min_avail, avail)
        if agg > peak_agg[0]:
            peak_agg = (agg, now)
        peak_workers = max(peak_workers, workers)
        sw.writerow([f"{now:.1f}", avail, agg, workers, lake_rss])
        time.sleep(ns.interval)
        status = child.poll()
    wall = time.time() - t0
    samples.close()

    rows = sorted(procs.values(), key=lambda r: r["start"])
    with open(os.path.join(ns.out, "modules.csv"), "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["module", "kind", "start_s", "end_s", "elapsed_s", "peak_rss_mib"])
        for r in rows:
            w.writerow([r["module"], r["name"], f"{r['start']:.1f}", f"{r['end']:.1f}",
                        f"{r['end'] - r['start']:.1f}", f"{r['hwm'] / 1024:.0f}"])
    with open(os.path.join(ns.out, "oleans.csv"), "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["olean", "mtime_rel_s", "bytes"])
        for p, m, s in sorted(scan_oleans(os.getcwd()), key=lambda x: x[1]):
            w.writerow([p, f"{m - t0:.1f}", s])
    summary = {
        "cmd": cmd,
        "exit_status": status,
        "killed": status in (137, -signal.SIGKILL),
        "wall_s": round(wall, 1),
        "min_mem_available_mib": round(min_avail / 1024),
        "peak_lean_rss_mib": round(peak_agg[0] / 1024),
        "peak_lean_rss_at_s": round(peak_agg[1], 1),
        "peak_lean_workers": peak_workers,
        "lean_processes": sum(1 for r in rows if r["name"] == "lean"),
        "kernel_oom": [l for l in kernel_oom_lines() if l not in dmesg_before],
    }
    with open(os.path.join(ns.out, "summary.json"), "w") as f:
        json.dump(summary, f, indent=1)
    print(json.dumps(summary), file=sys.stderr)
    sys.exit(status if status >= 0 else 128 - status)


if __name__ == "__main__":
    main()
