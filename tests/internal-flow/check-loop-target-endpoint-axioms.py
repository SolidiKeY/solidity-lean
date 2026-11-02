#!/usr/bin/env python3
"""Exact builtin kernel axiom inventory; not a complete source or full gate."""
import json
from pathlib import Path
import re
import sys
PINS = {'Solidity.Backend.InternalFlow.LoopTargetChecks.actual_endpoint': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.LoopTargetChecks.represented_endpoint': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.LoopTargetChecks.whole_target_actual': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.LoopTargetChecks.wrong_loop_cost': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.LoopTargetChecks.complete_endpoint': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.LoopTargetChecks.compiler_input_agrees': ['Classical.choice', 'Quot.sound', 'propext']}
NAMES = ['Solidity.Backend.InternalFlow.LoopTargetChecks.actual_endpoint', 'Solidity.Backend.InternalFlow.LoopTargetChecks.represented_endpoint', 'Solidity.Backend.InternalFlow.LoopTargetChecks.whole_target_actual', 'Solidity.Backend.InternalFlow.LoopTargetChecks.wrong_loop_cost', 'Solidity.Backend.InternalFlow.LoopTargetChecks.complete_endpoint', 'Solidity.Backend.InternalFlow.LoopTargetChecks.compiler_input_agrees']
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
