#!/usr/bin/env python3
"""Generate additive owned Bridge imports only."""
from pathlib import Path
root=Path(__file__).resolve().parents[1]
p=root/'Bridge/SolidityBridge.lean'
s=p.read_text()
for name in ('LinkedCycle','LinkedCycleControls'):
    assert (root/('Bridge/SolidityBridge/RoadmapV15/P10/'+name+'.lean')).is_file()
    line='import SolidityBridge.RoadmapV15.P10.'+name
    if line not in s.splitlines():s+='\n'+line+'\n'
p.write_text(s)
