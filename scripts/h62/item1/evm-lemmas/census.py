#!/usr/bin/env python3
"""Print a deterministic source census for H62 item 11; read-only, no generated files."""
from pathlib import Path
import re

root = Path(__file__).resolve().parents[4]
patterns = {
    "cons_revert": re.compile(r'\b(?:theorem|lemma)\s+run_cons_revert\b'),
    "pushes_zero": re.compile(r'\b(?:theorem|lemma)\s+(?:StmtFrag|ProgFrag)\.pushes_zero\b'),
    "allocation_zero_cons": re.compile(r'\b(?:theorem|lemma)\s+allocationCostProg_(?:zero|cons)\b'),
    "loc_inequality": re.compile(r'(?:Loc\.data.*≠|≠.*Loc\.data)'),
}
for label, pattern in patterns.items():
    print(f'[{label}]')
    for area in (root / 'Solidity/Evm', root / 'Solidity/Backend', root / 'Solidity/Lowering'):
        for path in sorted(area.rglob('*.lean')):
            if (area.name == 'Evm' and 'Examples' in path.name) or ('MemoryCopies' in path.parts and 'Controls' in path.name):
                continue
            for n, line in enumerate(path.read_text().splitlines(), 1):
                if pattern.search(line):
                    print(f'{path.relative_to(root)}:{n}:{line.strip()}')
