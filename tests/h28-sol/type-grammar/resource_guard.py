"""Task-local headroom and exclusive heavy-runtime lock."""
import fcntl,pathlib

def available_bytes(meminfo=pathlib.Path('/proc/meminfo'), cgroup=pathlib.Path('/sys/fs/cgroup')):
    host=int(next(line.split()[1] for line in meminfo.read_text().splitlines() if line.startswith('MemAvailable:')))*1024
    maximum=(cgroup/'memory.max').read_text().strip()
    if maximum=='max': return host
    return min(host,int(maximum)-int((cgroup/'memory.current').read_text()))

def heavy_lock():
    lock=open('/tmp/solidity-lean-feature-groups-20261025/h28-type-heavy.lock','a')
    try:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    except BlockingIOError:
        raise SystemExit("Another task heavy runtime is active; stop it first")
    return lock
