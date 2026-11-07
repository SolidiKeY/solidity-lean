"""Serial command measurement. The enclosing Docker scope supplies hard limits."""
import json, os, pathlib, resource, subprocess, sys, time
assert pathlib.Path('/sys/fs/cgroup/memory.max').read_text().strip() == '12884901888'
assert pathlib.Path('/sys/fs/cgroup/memory.swap.max').read_text().strip() == '0'
assert os.environ['LEAN_NUM_THREADS'] == '1'
# The outer VM has a 16 GiB cap. Reserve H1's 4 GiB before each command.
mem = dict((k, int(v.split()[0])) for k, v in (line.split(':', 1) for line in pathlib.Path('/proc/meminfo').read_text().splitlines()))
assert mem['MemAvailable'] * 1024 >= 4 * 1024**3, 'H1 available memory reserve'
start = time.monotonic()
result = subprocess.run(sys.argv[1:])
print(json.dumps({'command': sys.argv[1:], 'exit': result.returncode,
                  'wallSeconds': time.monotonic()-start,
                  'childMaxRssKiB': resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
                  'scopeMemoryPeakBytes': pathlib.Path('/sys/fs/cgroup/memory.peak').read_text().strip()}, sort_keys=True), flush=True)
sys.exit(result.returncode)
