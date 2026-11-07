import pathlib, subprocess, sys, time
container = sys.argv[1]
peak = 0
minimum = 16 * 1024**3
started = False
launch = time.monotonic()
while True:
    state = subprocess.run(["docker", "--host=unix:///var/run/docker.sock", "inspect", "--format", "{{.State.Status}}", container], capture_output=True, text=True).stdout.strip()
    if state == "running":
        started = True
    elif state == "created" and not started and time.monotonic() - launch < 30:
        time.sleep(0.1)
        continue
    else:
        break
    used = int(pathlib.Path("/sys/fs/cgroup/memory.current").read_text())
    cap = int(pathlib.Path("/sys/fs/cgroup/memory.max").read_text())
    available = next(int(x.split()[1])*1024 for x in pathlib.Path("/proc/meminfo").read_text().splitlines() if x.startswith("MemAvailable:"))
    reserve = min(cap-used, available)
    peak = max(peak, used)
    minimum = min(minimum, reserve)
    if reserve < 4 * 1024**3:
        subprocess.run(["docker", "--host=unix:///var/run/docker.sock", "stop", "--time", "1", container], check=True)
        print("RESERVE_STOP", reserve, flush=True)
        sys.exit(1)
    time.sleep(0.5)
print("OUTER_PEAK_BYTES", peak, "RESERVE_MIN_BYTES", minimum, "STARTED", started, flush=True)
