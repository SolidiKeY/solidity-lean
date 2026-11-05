#!/usr/bin/env python3
"""Record exact kernel child rusage (maximum per-process RSS, not aggregate)."""
import json,pathlib,resource,subprocess,sys,time
out=pathlib.Path(sys.argv[1]); command=sys.argv[2:]
if out.exists(): raise SystemExit('refusing to overwrite rusage record')
start=time.monotonic(); result=subprocess.run(command)
usage=resource.getrusage(resource.RUSAGE_CHILDREN)
out.write_text(json.dumps(dict(command=command,exit=result.returncode,elapsed_seconds=time.monotonic()-start,children_user_seconds=usage.ru_utime,children_system_seconds=usage.ru_stime,children_max_rss_kib=usage.ru_maxrss,children_major_faults=usage.ru_majflt,children_minor_faults=usage.ru_minflt),indent=2)+'\n')
raise SystemExit(result.returncode)
