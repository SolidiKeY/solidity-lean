#!/usr/bin/env python3
"""Run exactly one command, recording this hard-limited container's resources."""
import hashlib, json, os, subprocess, sys, time
from pathlib import Path
assert Path('/sys/fs/cgroup/memory.max').read_text().strip() == '12884901888'
assert Path('/sys/fs/cgroup/memory.swap.max').read_text().strip() == '0'
assert os.environ['LEAN_NUM_THREADS'] == '1'
name = sys.argv[1]
out = Path('tests/sol-expression-uniqueness/evidence')
source_hashes = {p.as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
                 for p in Path("Solidity/Frontend/ExpressionUniqueness").rglob("*.lean")}
verification_hashes = {p.as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
                       for p in Path("tests/sol-expression-uniqueness").rglob("*.lean")}
start = time.monotonic()
p = subprocess.Popen(sys.argv[2:])
peak = 0
while True:
    peak = max(peak, int(Path('/sys/fs/cgroup/memory.current').read_text()))
    pid, status, usage = os.wait4(p.pid, os.WNOHANG)
    if pid:
        break
    time.sleep(0.2)
code = os.waitstatus_to_exitcode(status)
result = dict(command=sys.argv[2:], exit=code, wall_seconds=time.monotonic()-start,
              child_peak_rss_kib=usage.ru_maxrss, sampled_cgroup_peak_bytes=peak,
              memory_max=12884901888, memory_swap_max=0, lean_num_threads=1, source_hashes=source_hashes, verification_hashes=verification_hashes,
              cgroup_memory_peak_bytes=int(Path("/sys/fs/cgroup/memory.peak").read_text()),
              memory_events=Path("/sys/fs/cgroup/memory.events").read_text())
(out/(name+'.inside.json')).write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result), flush=True)
sys.exit(code)
