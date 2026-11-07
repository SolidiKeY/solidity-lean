#!/usr/bin/env python3
"""Matched median timing gate; exit 2 on >10% slowdown, no budget changes."""
import argparse
import json
from pathlib import Path
import statistics

ap = argparse.ArgumentParser()
ap.add_argument('--before', type=Path, nargs='+', required=True)
ap.add_argument('--after', type=Path, nargs='+', required=True)
ap.add_argument('--output', type=Path, required=True)
a = ap.parse_args()
before = [json.loads(p.read_text()) for p in a.before]
after = [json.loads(p.read_text()) for p in a.after]
assert len(before) >= 3 and len(after) >= 3, 'need three samples per side'
for r in before+after:
    assert r['exit'] == 0 and not r['stop_reason'], 'failed run is not a timing sample'
    assert r['command'] == before[0]['command'], 'commands differ'
    assert r['context'] == before[0]['context'], 'tree/cache/resources differ'
b = statistics.median(r['wall_seconds'] for r in before)
c = statistics.median(r['wall_seconds'] for r in after)
ratio = c/b-1
out = {'before_median_seconds': b, 'after_median_seconds': c,
       'slowdown_fraction': ratio, 'status': 'stop' if c > b * 1.10 else 'pass',
       'context': before[0]['context'], 'command': before[0]['command']}
a.output.write_text(json.dumps(out, indent=2)+'\n')
print(json.dumps(out))
raise SystemExit(2 if c > b * 1.10 else 0)
