#!/usr/bin/env python3
"""Owned serial validation runner: 12 GiB cgroup, no swap, 4 GiB reserve.
No inherited remote Docker endpoint; preserves credentials and proxy settings.
"""
import fcntl, hashlib, json, os, shlex, subprocess, sys, time, signal
from pathlib import Path
root = Path(__file__).resolve().parents[3]
evidence = root / "tests/fullscope-20261104/vo1/evidence"
label, *command = sys.argv[1:]
if not command or not label.replace("-", "").isalnum():
    raise SystemExit("usage: bounded.py LABEL COMMAND...")
lock = open("/tmp/solidity-lean-feature-groups-20261025/writer.lock", "a")
fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
GiB = 1024**3
cg = Path("/sys/fs/cgroup")
def available():
    host = int(next(s.split()[1] for s in Path("/proc/meminfo").read_text().splitlines() if s.startswith("MemAvailable:"))) * 1024
    cap = (cg / "memory.max").read_text().strip()
    return min(host, int(cap) - int((cg / "memory.current").read_text())) if cap != "max" else host
if available() < 4 * GiB:
    raise SystemExit("4 GiB admission reserve unavailable")
for executable in ["lean", "lake"]:
    probe = subprocess.run(["pgrep", "-x", executable], capture_output=True)
    if probe.returncode != 1:
        raise SystemExit("Existing or uninspectable Lean/Lake process: preserve and inspect")
env = os.environ.copy()
for key in ["DOCKER_HOST", "DOCKER_CONTEXT", "DOCKER_TLS", "DOCKER_TLS_VERIFY", "DOCKER_CERT_PATH"]:
    env.pop(key, None)
docker = ["docker", "--host=unix:///var/run/docker.sock"]
# Initial prerequisite runs lack exact walls; charge their full 180s+300s caps.
records = [json.loads(p.read_text()) for p in evidence.glob("*.json")]
charged = 480 + sum(r["wall_seconds"] for r in records if isinstance(r, dict) and "wall_seconds" in r)
# A killed monitor must not erase its time reservation.
initial = {"runtime-keysort", "interface-build"}
orphans = {p.stem for p in evidence.glob("*.log")} | {p.stem for p in evidence.glob("*.reservation")}
charged += 300 * sum(1 for stem in orphans if stem not in initial and not (evidence / (stem + ".json")).exists())
if charged + 300 > 14400:
    raise SystemExit("aggregate 14400s budget exhausted; no further heavy check")
name = "vo1-" + label + "-" + str(os.getpid())
script = "set -eu; test \"$(cat /sys/fs/cgroup/memory.max)\" = 12884901888; test \"$(cat /sys/fs/cgroup/memory.swap.max)\" = 0; source /workspace/.setup/activate.sh; export LEAN_NUM_THREADS=1; export PATH=/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:$PATH; trap 'printf CGROUP_PEAK_BYTES=; cat /sys/fs/cgroup/memory.peak' EXIT; " + shlex.join(["timeout", "--signal=TERM", "--kill-after=2", "290", *command])
args = docker + ["run", "--rm", "--name", name, "--network=none", "--memory=12g", "--memory-swap=12g", "--cpus=1", "--user=1000:1000", "-v", "/workspace:/workspace", "-v", "/opt:/opt:ro", "-v", "/usr:/usr:ro", "-w", str(root), "ubuntu@sha256:fe81560990fae86dc4743202b2cb4d3df98d0bcf949173cecef15ce1127ef852", "bash", "-c", script]
evidence.mkdir(exist_ok=True)
log = evidence / (label + ".log")
receipt = evidence / (label + ".json")
reservation = evidence / (label + ".reservation")
if log.exists() or receipt.exists() or reservation.exists():
    raise SystemExit("preserve existing evidence: choose a fresh label")
reservation.write_text("Reserved 300 seconds before launch; retain if receipt is missing.\n")
started = time.monotonic()
head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
peak = 0
samples = 0
stopped = None
error = None
cleanup_verified = False
proc = None
def fingerprint():
    names = subprocess.check_output(["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard"], cwd=root).decode().split("\0")
    paths = [root / n for n in names if n and (n.endswith((".lean", ".toml")) or n.startswith("scripts/") or n in ("lean-toolchain", "lake-manifest.json", "run-lean.sh") or n.startswith("tests/fullscope-20261104/vo1/") and n.endswith((".py", ".sh", "/lake")))]
    return {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(set(paths)) if p.is_file()}

def terminated(signum, frame):
    raise RuntimeError("monitor received signal " + str(signum))
signal.signal(signal.SIGTERM, terminated)
source_before = fingerprint()
with log.open("w") as out:
    out.write("$ " + shlex.join(args) + "\n"); out.flush()
    try:
        proc = subprocess.Popen(args, env=env, stdout=out, stderr=subprocess.STDOUT)
        while proc.poll() is None:
            top = subprocess.run(docker + ["top", name, "-eo", "pid,rss"], env=env, text=True, capture_output=True, timeout=10)
            if top.returncode == 0:
                rss = sum(int(line.split()[1]) * 1024 for line in top.stdout.splitlines()[1:] if len(line.split()) == 2)
                peak = max(peak, rss); samples += 1
            if available() < 4 * GiB or peak > 12 * GiB or time.monotonic() - started > 300:
                stopped = "resource/time guard"
                break
            time.sleep(0.5)
    except BaseException as exc:
        error = type(exc).__name__ + ": " + str(exc)
    finally:
        try:
            if proc is not None and proc.poll() is None:
                subprocess.run(docker + ["stop", "-t", "1", name], env=env, stdout=out, stderr=subprocess.STDOUT, timeout=15)
            code = proc.wait(timeout=20) if proc is not None else 125
            inspection = subprocess.run(docker + ["ps", "-aq", "--filter", "name=^/" + name + "$"], env=env, text=True, capture_output=True, timeout=10)
            cleanup_verified = inspection.returncode == 0 and not inspection.stdout.strip()
        except BaseException as exc:
            code = 125
            error = (error or "") + "; cleanup: " + type(exc).__name__ + ": " + str(exc)
source_after = fingerprint()
import re
cgroup_peaks = re.findall(r"CGROUP_PEAK_BYTES=(\d+)", log.read_text())
cgroup_peak = int(cgroup_peaks[-1]) if cgroup_peaks else None
runner_exit = code if code else (1 if stopped or error or not cleanup_verified or source_before != source_after or samples == 0 or cgroup_peak is None or cgroup_peak > 12 * GiB else 0)
record = dict(runner_exit=runner_exit, child_exit=code, charged_before_seconds=charged, cgroup_peak_bytes=cgroup_peak, command=command, container_command=args, head=head, exit=code,
              wall_seconds=time.monotonic()-started, peak_aggregate_rss_bytes=peak,
              samples=samples, guard_stop=stopped, monitor_error=error, cleanup_verified=cleanup_verified, source_sha256=source_before, source_unchanged=(source_before == source_after), log_sha256=hashlib.sha256(log.read_bytes()).hexdigest())
receipt.write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps({k: v for k, v in record.items() if k not in ("source_sha256", "container_command")}))
raise SystemExit(runner_exit)
