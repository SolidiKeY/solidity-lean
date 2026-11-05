#!/usr/bin/env python3
"""Linux child-process timing/RSS; aggregate memory is separately cgroup-enforced."""
import json,pathlib,resource,subprocess,sys,time
label=sys.argv[1];command=sys.argv[2:];start=time.monotonic()
p=subprocess.run(command)
r=resource.getrusage(resource.RUSAGE_CHILDREN)
row=dict(command=command,exit=p.returncode,seconds=round(time.monotonic()-start,6),peak_child_rss_kib=r.ru_maxrss,user_seconds=r.ru_utime,system_seconds=r.ru_stime)
pathlib.Path('tests/sol-numeric-literals/evidence/'+label+'.timing.json').write_text(json.dumps(row,indent=2)+'\n')
print(json.dumps(row));sys.exit(p.returncode)
