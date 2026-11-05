#!/usr/bin/env python3
"""H14 append-only registration of the owned computed producer modules."""
from pathlib import Path
import argparse
ROOT=Path(__file__).resolve().parents[2]
MODULES=["Solidity.Lowering.V07.LocationGraphProducer","Solidity.Lowering.V07.LocationProducerControls","Solidity.Lowering.V07.RankConvergence","Solidity.Lowering.V07.NodeRank","Solidity.Lowering.V07.FieldCompleteness"]
p=argparse.ArgumentParser();p.add_argument("--check",action="store_true");a=p.parse_args()
f=ROOT/"Solidity.lean";text=f.read_text()
for m in MODULES:
    assert (ROOT/(m.replace(".","/")+".lean")).exists(),m
    line="import "+m;count=text.splitlines().count(line)
    assert count<=1,"duplicate registration: "+m
    if a.check:assert count==1,"missing generated registration: "+m
    elif not count:text+="\n-- H14 generated producer registration.\n"+line+"\n"
if not a.check:f.write_text(text)
print("H14 producer registrations match" if a.check else "H14 producer registrations generated")
