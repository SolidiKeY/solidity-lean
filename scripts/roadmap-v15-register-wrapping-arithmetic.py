#!/usr/bin/env python3
"""Append only owned Bridge registrations; never edits Solidity.lean."""
from pathlib import Path
root=Path(__file__).resolve().parents[1]
modules=('WrappingArithmeticConsumer','WrappingArithmeticControls')
p=root/'Bridge/SolidityBridge.lean'
assert not p.is_symlink()
text=p.read_text();new=[]
for module in modules:
 source=root/('Bridge/SolidityBridge/RoadmapV15/P10/'+module+'.lean')
 assert source.is_file() and not source.is_symlink()
 line='import SolidityBridge.RoadmapV15.P10.'+module
 if line not in text.splitlines():new.append(line)
if new:p.write_text(text+'\n'+'\n'.join(new)+'\n')
print('Bridge registrations appended: '+str(len(new))+'; Solidity.lean unchanged')
