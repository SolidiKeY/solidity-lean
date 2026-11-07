#!/usr/bin/env python3
"""Second explicit embedded tranche, prefix Checks. External audit, no proof."""
import argparse
import hashlib
import json
from pathlib import Path
import embedded
from census import ROOT
from classify import INVENTORY_SHA256
REGIONS = {
 "RuntimeFrameV3ParentPrefixes.lean": (100,172),
 "RuntimeFrameV3AllocatingPrefixes.lean": (114,250),
 "RuntimeFrameV3MutatingPrefixes.lean": (102,349),
}
FACETS = dict(embedded.FACETS, growthneg="Exact GrowsAllocator budget fails; not nonexistence of allocator ownership or inequality of computed allocation cost")
MAP = ROOT / "tests/h62/item4/generic-internalflow/prefix-cases.txt"
def classify(inventory, mapping):
 result=embedded.classify(inventory,mapping,regions=REGIONS,facet_definitions=FACETS)
 result['scope']='Only three explicit prefix Checks regions; prior four-region tranche and57Controls are separate. Other embedded controls and full proof queue remain pending.'
 return result
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--inventory',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 data=a.inventory.read_bytes()
 if hashlib.sha256(data).hexdigest()!=INVENTORY_SHA256:raise SystemExit('frozen inventory mismatch')
 output=a.output.resolve()
 if output.is_relative_to(ROOT.resolve()) or output==a.inventory.resolve() or (output.exists() and output.samefile(a.inventory)):raise SystemExit('output must be off git and distinct from frozen inventory')
 result=classify(json.loads(data),embedded.parse(MAP.read_text(),regions=REGIONS,facet_definitions=FACETS))
 encoded=json.dumps(result,sort_keys=True,ensure_ascii=False,indent=2)+'\n';output.write_text(encoded)
 print(json.dumps({**result['summary'],'sha256':hashlib.sha256(encoded.encode()).hexdigest()}))
if __name__=='__main__':main()
