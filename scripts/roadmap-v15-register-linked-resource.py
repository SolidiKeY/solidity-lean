#!/usr/bin/env python3
"""Append generated owned Bridge imports; never changes Solidity.lean."""
from pathlib import Path
root=Path(__file__).resolve().parents[1]
p=root/'Bridge/SolidityBridge.lean'
text=p.read_text()
for name in ('LinkedResourceBounds','LinkedResourceControls'):
    assert (root/('Bridge/SolidityBridge/RoadmapV15/P10/'+name+'.lean')).is_file()
    line='import SolidityBridge.RoadmapV15.P10.'+name
    if line not in text.splitlines(): text+='\n'+line+'\n'
p.write_text(text)
