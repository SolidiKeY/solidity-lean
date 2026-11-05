#!/usr/bin/env python3
"""Measure a single native external test; no Lean environment is created."""
import json
from pathlib import Path
import resource
import subprocess
import sys
import time
start = time.monotonic()
result = subprocess.run(sys.argv[1:])
usage = resource.getrusage(resource.RUSAGE_CHILDREN)
record = {'command': sys.argv[1:], 'exit': result.returncode,
          'wall_s': round(time.monotonic() - start, 6),
          'user_s': usage.ru_utime, 'system_s': usage.ru_stime,
          'max_rss_kib': usage.ru_maxrss,
          'boundary': 'external native intrinsic-model execution, not ordinary verifier or EVM equivalence'}
(Path(__file__).resolve().parent / 'evidence/native-execution.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record), flush=True)
raise SystemExit(result.returncode)
