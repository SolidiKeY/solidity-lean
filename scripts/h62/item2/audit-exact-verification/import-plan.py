#!/usr/bin/env python3
"""Source import closure for the two first audit interfaces; no cache reuse."""
import re
from pathlib import Path
from census import mask

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
for name in ("Solidity.Corpus.Basic", "Solidity.Calculus.ExactReduction"): visit(name)
print("\n".join(order))
