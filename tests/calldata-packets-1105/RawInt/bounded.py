#!/usr/bin/env python3
"""Owned Docker scope with a host memory-reserve guard and writer lock."""
import fcntl, json, os, pathlib, subprocess, sys, time, uuid
root=pathlib.Path(__file__).resolve().parents[3]
lock=pathlib.Path('/tmp/solidity-lean-feature-groups-20261025/writer.lock')
lock.parent.mkdir(parents=True,exist_ok=True)
name='raw-int-1105-'+uuid.uuid4().hex[:12]
def host_available():
    for line in pathlib.Path('/proc/meminfo').read_text().splitlines():
        if line.startswith('MemAvailable:'): return int(line.split()[1])*1024
def parent_current(): return int(pathlib.Path('/sys/fs/cgroup/memory.current').read_text())
def available():
    limit=pathlib.Path('/sys/fs/cgroup/memory.max').read_text().strip()
    return min(host_available(), int(limit)-parent_current()) if limit!='max' else host_available()
def container_rss(cid):
    total=0
    if not cid: return 0
    for proc in pathlib.Path('/proc').glob('[0-9]*'):
        try:
            if cid in (proc/'cgroup').read_text():
                total+=int((proc/'statm').read_text().split()[1])*os.sysconf('SC_PAGE_SIZE')
        except (OSError,ValueError,IndexError): pass
    return total
with lock.open('a') as held:
    fcntl.flock(held,fcntl.LOCK_EX)
    if available()<4*1024**3: raise SystemExit('H1 reserve unavailable')
    status=subprocess.check_output(['git','status','--short'],cwd=root,text=True)
    print('writer lock held; checkout status entries='+str(len(status.splitlines())),flush=True)
    config=root/'tests/calldata-packets-1105/RawInt/lakefile.worker.toml'
    if config.exists(): raise SystemExit('unexpected existing worker config; preserve and inspect')
    text=(root/'lakefile.toml').read_text().replace('weakLeanArgs = ["--tstack=131072"]','weakLeanArgs = ["--tstack=131072", "-j1"]')
    text=text.replace('[[lean_exe]]','[[lean_exe]]\nweakLeanArgs = ["--tstack=131072", "-j1"]')
    text=text.replace('srcDir = "vendor/LeanTeX"','srcDir = "vendor/LeanTeX"\nweakLeanArgs = ["--tstack=131072", "-j1"]')
    config.write_text(text)
    logs=root/'tests/calldata-packets-1105/RawInt/evidence/runtime'; logs.mkdir(parents=True,exist_ok=True)
    metrics=logs/(name+'.cgroup')
    cmd=['docker','run','--rm','--name',name,'--memory=12g','--memory-swap=12g','--cpus=1','--user=1000:1000','--env','SOL_CB_METRICS='+str(metrics),'-v','/workspace:/workspace','-v','/opt:/opt:ro','-v','/usr:/usr:ro','-w',str(root),'ubuntu@sha256:fe81560990fae86dc4743202b2cb4d3df98d0bcf949173cecef15ce1127ef852','bash','-c',
        'set -eu; test "$(cat /sys/fs/cgroup/memory.max)" = 12884901888; test "$(cat /sys/fs/cgroup/memory.swap.max)" = 0; source /workspace/.setup/activate.sh; export LEAN_NUM_THREADS=1; set +e; "$@"; result=$?; { cat /sys/fs/cgroup/memory.max; cat /sys/fs/cgroup/memory.swap.max; cat /sys/fs/cgroup/memory.peak; } > "$SOL_CB_METRICS"; exit $result','bounded',*sys.argv[1:]]
    start=time.monotonic(); child=subprocess.Popen(cmd); minimum=available(); peak_parent=parent_current(); peak_rss=0; cid=None
    try:
        while child.poll() is None:
            minimum=min(minimum,available()); peak_parent=max(peak_parent,parent_current())
            if cid is None:
                probe=subprocess.run(['docker','inspect','-f','{{.Id}}',name],text=True,capture_output=True)
                if probe.returncode==0: cid=probe.stdout.strip()
            peak_rss=max(peak_rss,container_rss(cid))
            if minimum<4*1024**3:
                subprocess.run(['docker','stop','--time','5',name],check=False)
                child.wait(); raise SystemExit('H1 reserve breached; stopped owned container')
            time.sleep(.5)
    finally:
        if child.poll() is None:
            subprocess.run(['docker','stop','--time','5',name],check=False);child.wait()
        config.unlink()
        report=dict(checkout_status=status,command=sys.argv[1:],exit=child.returncode,elapsed_seconds=time.monotonic()-start,minimum_reserve_bytes=minimum,peak_parent_memory_current=peak_parent,peak_sampled_aggregate_rss_bytes=peak_rss)
        if metrics.exists(): report['job_memory_max_swap_max_peak']=metrics.read_text().splitlines()
        (logs/(name+'.json')).write_text(json.dumps(report,indent=2)+'\n')
        print('bounded: '+json.dumps({k:v for k,v in report.items() if k!='checkout_status'}),flush=True)
    raise SystemExit(child.returncode)
