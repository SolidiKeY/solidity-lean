#!/usr/bin/env python3
"""Guard actual unmodified builtin reports for the primitive caller-value transport consumers.
Run on the separately checked import query; it does not replace kernel checking
or the unchanged original542-report fixture inventory.
"""
import json
from pathlib import Path
import re
import sys
NAMES = ['Solidity.Backend.InternalFlow.CallerView.value_drop', 'Solidity.Backend.InternalFlow.CallerView.represented_value_drop', 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.final_target_values', 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.final_wrong_scalar_destination']
PINS = {'Solidity.Backend.InternalFlow.CallerView.value_drop': ['propext'], 'Solidity.Backend.InternalFlow.CallerView.represented_value_drop': ['Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.final_target_values': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.final_wrong_scalar_destination': ['Classical.choice', 'Quot.sound', 'propext']}
PATTERN = r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
def check(text):
    if re.search(r"(?:^|\n).*?(?:error:|error\(|sorryAx)", text):
        raise ValueError("diagnostic or untrusted axiom in builtin audit")
    reports = [(n, sorted(x.strip() for x in a.split(',') if x.strip()))
               for n, a in re.findall(PATTERN, text)]
    expected = [(n, PINS[n]) for n in NAMES]
    if reports != expected:
        raise ValueError("missing, reordered, duplicate or changed caller-value axiom report")
    return len(reports)
if __name__ == '__main__':
    try:
        count = check(Path(sys.argv[1]).read_text())
    except (ValueError, OSError, IndexError) as error:
        print(str(error), file=sys.stderr)
        sys.exit(1)
    print(json.dumps({'status': 'pass', 'actual_builtin_reports': count}))
