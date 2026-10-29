#!/usr/bin/env python3
"""Task-local serial Docker resource guard and evidence recorder (no Lean server)."""
import json, os, pathlib, subprocess, sys, time
label, *command = sys.argv[1:]
root = pathlib.Path(__file__).resolve().parents[2]
evidence = pathlib.Path('/workspace/scratch/storage-values-evidence')
evidence.mkdir(exist_ok=True)
limit = 12 * 1024**3
outer = pathlib.Path('/sys/fs/cgroup')
maximum = (outer/'memory.max').read_text().strip()
current = int((outer/'memory.current').read_text())
if maximum != 'max' and int(maximum) - current < limit + 1024**3:
    raise SystemExit('insufficient enclosing cgroup headroom')
env = os.environ.copy()
for key in ['DOCKER_HOST','DOCKER_CONTEXT','DOCKER_TLS','DOCKER_TLS_VERIFY','DOCKER_CERT_PATH']:
    env.pop(key, None)
docker = ['docker', '--host=unix:///var/run/docker.sock']
name = 'storage-values-' + str(os.getpid())
args = docker + ['run','--rm','--name',name,'--network','none',
    '--memory',str(limit),'--memory-swap',str(limit),'--user','1000:1000',
    '--mount','type=bind,src=/workspace,dst=/workspace',
    '--mount','type=bind,src=/usr,dst=/usr,readonly',
    '--mount','type=bind,src=/lib,dst=/lib,readonly',
    '--mount','type=bind,src=/lib64,dst=/lib64,readonly',
    '-w',str(root),'-e','LEAN_NUM_THREADS=1',
    '-e','PATH=/workspace/.setup/tools/lean-4.24.0-linux/bin:/usr/bin:/bin',
    'ubuntu:24.04','sh','-c',
    'cat /sys/fs/cgroup/memory.max /sys/fs/cgroup/memory.swap.max; "$@"; r=$?; echo CGROUP_PEAK; cat /sys/fs/cgroup/memory.peak; exit "$r"',
    'bounded'] + command
started = time.monotonic()
peak_rss = 0
with (evidence/(label+'.log')).open('w') as log:
    process = subprocess.Popen(args, env=env, stdout=log, stderr=subprocess.STDOUT)
    while process.poll() is None:
        top = subprocess.run(docker+['top',name,'-eo','rss'],env=env,capture_output=True,text=True)
        if top.returncode == 0:
            peak_rss = max(peak_rss,sum(int(x) for x in top.stdout.splitlines()[1:] if x.strip().isdigit())*1024)
        time.sleep(0.5)
    code = process.wait()
record = dict(command=command, exit=code, seconds=time.monotonic()-started,
    sampled_peak_aggregate_rss_bytes=peak_rss or None, memory_max=limit, swap_max=0,
    enclosing_memory_max=maximum, enclosing_memory_current_before=current)
(evidence/(label+'.json')).write_text(json.dumps(record,indent=2)+'\n')
print((evidence/(label+'.log')).read_text())
print(json.dumps(record))
raise SystemExit(code)
