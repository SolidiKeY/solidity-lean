#!/usr/bin/env python3
"""Generate additive registration of the checked producer only."""
from pathlib import Path
root=Path(__file__).resolve().parents[1]
name='SolidityBridge.RoadmapV15.P10.InvocationEnvironment'
p=root/'Bridge/SolidityBridge.lean'
assert (root/'Bridge'/Path(*name.split('.'))).with_suffix('.lean').is_file()
s=p.read_text()
if 'import '+name not in s.splitlines():p.write_text(s+'\nimport '+name+'\n')
