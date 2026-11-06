#!/usr/bin/env python3
"""Source import closure for the two first audit interfaces; no cache reuse."""
import argparse
from pathlib import Path
from census import mask

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("targets", nargs="*", help="Solidity module names; default: first two audit interfaces")
args = parser.parse_args()
root = Path.cwd()
seen = set()
order = []
def visit(name):
    if name in seen: return
    seen.add(name)
    path = root / (name.replace(".", "/")+".lean")
    for row in mask(path.read_text()).splitlines():
        if not row.startswith("import "): continue
        for child in row.split()[1:]:
            if child.startswith("Solidity."): visit(child)
    order.append(name.replace(".", "/"))
for name in (args.targets or ["Solidity.Corpus.Basic", "Solidity.Calculus.ExactReduction"]): visit(name)
print("\n".join(order))
