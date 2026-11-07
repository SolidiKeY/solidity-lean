"""Execute one serial gate inside the coordinator's exact bounded container."""
import json
import hashlib
import os
import pathlib
import resource
import signal
import subprocess
import sys
import time

receipt = pathlib.Path(sys.argv[1])
command = sys.argv[2:]
if not command:
    raise SystemExit("usage: bounded-command.py RECEIPT COMMAND...")
scope = pathlib.Path("/sys/fs/cgroup")
outer = pathlib.Path("/task-outer-cgroup")
limit = int((scope / "memory.max").read_text())
swap = int((scope / "memory.swap.max").read_text())
if (limit, swap) != (12 * 1024**3, 0):
    raise SystemExit("refusing gate outside exact 12 GiB/no-swap scope")
if os.environ.get("LEAN_NUM_THREADS") != "1":
    raise SystemExit("LEAN_NUM_THREADS must be 1")
if receipt.exists():
    raise SystemExit("refusing to overwrite gate receipt")
reserve = 4 * 1024**3

def headroom():
    return int((outer / "memory.max").read_text()) - int((outer / "memory.current").read_text())

def rss():
    total = 0
    for proc in pathlib.Path("/proc").iterdir():
        if not proc.name.isdigit():
            continue
        try:
            total += int((proc / "statm").read_text().split()[1]) * os.sysconf("SC_PAGE_SIZE")
        except (FileNotFoundError, ProcessLookupError):
            pass
    return total

def persist(result):
    result["runnerSha256"] = hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()
    receipt.parent.mkdir(parents=True, exist_ok=True)
    temporary = receipt.with_name(receipt.name + ".tmp." + str(os.getpid()))
    temporary.write_text(json.dumps(result, indent=2)+"\n")
    try:
        os.link(temporary, receipt)  # Atomic publication; fails if destination exists.
    finally:
        temporary.unlink()

initial = headroom()
if initial < reserve:
    result = {"command": command, "exitCode": 125, "childStarted": False,
              "scope": {"memoryMaxBytes": limit, "memorySwapMaxBytes": swap},
              "requiredOuterHeadroomBytes": reserve, "initialOuterHeadroomBytes": initial,
              "resourceStop": True, "reason": "insufficient initial outer cgroup headroom"}
    persist(result)
    print(json.dumps(result), flush=True)
    raise SystemExit(125)
start = time.monotonic()
child = subprocess.Popen(command, start_new_session=True, env=dict(os.environ, NATIVE_BROWSER_BOUNDED_GATE="1"))
minimum, peak_rss, stopped = initial, 0, False
try:
    while child.poll() is None:
        available = headroom()
        minimum = min(minimum, available)
        peak_rss = max(peak_rss, rss())
        if available < reserve:
            stopped = True
            os.killpg(child.pid, signal.SIGKILL)
            break
        time.sleep(0.1)
    code = child.wait()
except BaseException:
    os.killpg(child.pid, signal.SIGKILL)
    child.wait()
    raise
usage = resource.getrusage(resource.RUSAGE_CHILDREN)
result = {
    "command": command, "exitCode": code, "wallSeconds": time.monotonic()-start,
    "scope": {"memoryMaxBytes": limit, "memorySwapMaxBytes": swap},
    "requiredOuterHeadroomBytes": reserve, "minimumOuterHeadroomBytes": minimum,
    "resourceStop": stopped, "sampledContainerProcessRssPeakBytes": peak_rss,
    "rssSamplingSeconds": 0.1, "childRusageMaxRssKiB": usage.ru_maxrss,
    "cgroupPeakBytes": int((scope / "memory.peak").read_text()),
    "cgroupEvents": (scope / "memory.events").read_text(),
}
persist(result)
print(json.dumps(result), flush=True)
raise SystemExit(125 if stopped else code)
