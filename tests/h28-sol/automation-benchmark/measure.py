#!/usr/bin/env python3
"""Measure one command using wait4/rusage; never treats a failure as success."""
import json
from pathlib import Path
import resource
import subprocess
import sys
import time
output, *command = sys.argv[1:]
started = time.monotonic()
process = subprocess.Popen(command)
code = process.wait()
usage = resource.getrusage(resource.RUSAGE_CHILDREN)
Path(output).write_text(json.dumps(dict(exit=code, wall_seconds=time.monotonic()-started,
    max_rss_kib=usage.ru_maxrss, user_seconds=usage.ru_utime,
    system_seconds=usage.ru_stime, rss_definition="Linux RUSAGE_CHILDREN maximum, not aggregate simultaneous RSS"), indent=2)+"\n")
raise SystemExit(code)
