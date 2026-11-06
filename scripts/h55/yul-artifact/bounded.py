#!/usr/bin/env python3
"""Run one serial task command, stopping if VM headroom falls below 4 GiB.
The runner refuses active swap. Each descendant inherits a 12 GiB
per-process address-space limit. Headroom is sampled every 100 ms, not
a hard aggregate RSS cap. This is a runtime guard, not a proof verdict.
"""
import json, os, pathlib, resource, signal, subprocess, sys, time
LIMIT = 12 * 1024**3
RESERVE = 4 * 1024**3
if len(sys.argv) < 4 or sys.argv[2] != "--":
    raise SystemExit("usage: bounded.py EVIDENCE_PREFIX -- COMMAND ARG...")
prefix = pathlib.Path(sys.argv[1])
prefix.parent.mkdir(parents=True, exist_ok=True)
def available():
    host = int(next(x.split()[1] for x in pathlib.Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:'))) * 1024
    cg = pathlib.Path('/sys/fs/cgroup')
    maximum = (cg / 'memory.max').read_text().strip()
    return min(host, int(maximum) - int((cg / 'memory.current').read_text())) if maximum != 'max' else host
def setup():
    resource.setrlimit(resource.RLIMIT_AS, (LIMIT, LIMIT))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
if len(pathlib.Path('/proc/swaps').read_text().splitlines()) != 1:
    raise SystemExit('refusing executor with active swap')
if available() < RESERVE:
    raise SystemExit('less than 4 GiB available before launch')
env = dict(os.environ, LEAN_NUM_THREADS='1')
start = time.monotonic()
reason = None
with prefix.with_suffix('.log').open('w') as log:
    child = subprocess.Popen(sys.argv[3:], stdout=log, stderr=subprocess.STDOUT, env=env, start_new_session=True, preexec_fn=setup)
    while child.poll() is None:
        if available() < RESERVE:
            reason = '4 GiB reserve exhausted'
        elif time.monotonic() - start > 600:
            reason = '600 second runtime bound exhausted'
        if reason:
            os.killpg(child.pid, signal.SIGKILL)
            break
        time.sleep(.1)
    code = child.wait()
record = dict(command=sys.argv[3:], exit_code=code, stop_reason=reason,
    wall_seconds=time.monotonic()-start, waited_child_maxrss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
    address_space_limit_bytes=LIMIT, reserve_bytes=RESERVE, lean_num_threads=1,
    swap_configured=False)
prefix.with_suffix('.json').write_text(json.dumps(record, indent=2)+'\n')
print(json.dumps(record))
raise SystemExit(code if code >= 0 else 128-code)
