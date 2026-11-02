#!/usr/bin/env python3
"""Exact builtin kernel axiom inventory; not a complete source or full gate."""
import json
from pathlib import Path
import re
import sys
PINS = {'Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.metrics': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.cost': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.need': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.flag': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.checked_need': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.checked_cost': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.stmt_run': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.prefix_cost': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.old_cost': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.old_need': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.stmt_cost': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.previous_run': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.total_room': ['Classical.choice', 'Quot.sound', 'propext']}
NAMES = ['Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.metrics', 'Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.cost', 'Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.need', 'Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.flag', 'Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.checked_need', 'Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.checked_cost', 'Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.stmt_run', 'Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.prefix_cost', 'Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.old_cost', 'Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.old_need', 'Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.stmt_cost', 'Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.previous_run', 'Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.total_room']
def check(text):
    if re.search(r"(?:^|\n).*?(?:error:|error\(|sorryAx)",text):
        raise ValueError("Lean diagnostic or untrusted axiom")
    rows = [(n,sorted(x.strip()for x in a.split(',')if x.strip()))
        for n,a in re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",text)]
    if rows != [(n,PINS[n])for n in NAMES]:
        raise ValueError("missing, extra, duplicate, reordered or changed axiom report")
    return len(rows)
log = Path(sys.argv[1]).read_text()
print(json.dumps({'status':'pass','reports':check(log)}))
