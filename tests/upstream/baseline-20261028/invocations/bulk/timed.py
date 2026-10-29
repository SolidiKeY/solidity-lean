import json,resource,subprocess,sys,time,pathlib
out=pathlib.Path(sys.argv[1]); start=time.monotonic()
with out.with_suffix('.log').open('w') as log:
 p=subprocess.run(sys.argv[2:],stdout=log,stderr=subprocess.STDOUT)
r=resource.getrusage(resource.RUSAGE_CHILDREN)
out.with_suffix('.json').write_text(json.dumps(dict(command=sys.argv[2:],exitCode=p.returncode,elapsedSeconds=time.monotonic()-start,maxChildRssKiB=r.ru_maxrss,userSeconds=r.ru_utime,systemSeconds=r.ru_stime,cgroupMemoryPeakBytes=int(pathlib.Path('/sys/fs/cgroup/memory.peak').read_text())),indent=2)+'\n')
print(out,p.returncode,flush=True)
sys.exit(p.returncode)
