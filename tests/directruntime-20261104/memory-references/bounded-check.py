"""Serial development-check observer; never produces a verifier verdict."""
import json, os, pathlib, signal, subprocess, sys, time
prefix, *command = sys.argv[1:]
assert command
assert pathlib.Path('/sys/fs/cgroup/memory.max').read_text().strip() == '12884901888'
assert pathlib.Path('/sys/fs/cgroup/memory.swap.max').read_text().strip() == '0'
assert os.environ.get('LEAN_NUM_THREADS') == '1'
def available():
    return int(next(s.split()[1] for s in pathlib.Path('/proc/meminfo').read_text().splitlines() if s.startswith('MemAvailable:'))) * 1024
assert available() >= 4*1024**3
started=time.monotonic(); peak=0; guard=False
with open(prefix+'.log','w') as log:
    proc=subprocess.Popen(command,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
    while proc.poll() is None:
        records={}
        for p in pathlib.Path('/proc').iterdir():
            if not p.name.isdigit(): continue
            try:
                fields=(p/'stat').read_text().rsplit(')',1)[1].split()
                records[int(p.name)]=(int(fields[1]),int(fields[21])*os.sysconf('SC_PAGE_SIZE')//1024)
            except (OSError,ValueError,IndexError): pass
        children={proc.pid}; pending=[proc.pid]
        while pending:
            parent=pending.pop()
            for pid,(ppid,_) in records.items():
                if ppid==parent and pid not in children: children.add(pid);pending.append(pid)
        peak=max(peak,sum(records.get(pid,(0,0))[1] for pid in children))
        if available() < 4*1024**3:
            guard=True;os.killpg(proc.pid,signal.SIGTERM);break
        time.sleep(.2)
    code=proc.wait()
receipt={'command':command,'exit':code,'wallSeconds':time.monotonic()-started,'peakAggregateRssKiB':peak,'headroomGuardStopped':guard,'memoryMax':12884901888,'memorySwapMax':0,'leanThreads':1}
pathlib.Path(prefix+'.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
sys.exit(code if not guard else 125)
