#!/usr/bin/env python3
"""Guard actual unmodified builtin reports for the captured caller-view consumer.
Run on the separately checked import query; it does not replace kernel checking
or the unchanged original542-report fixture inventory.
"""
import json
from pathlib import Path
import re
import sys
NAMES = ['Solidity.Backend.InternalFlow.CallerView.by_id', 'Solidity.Backend.InternalFlow.CallerView.reference', 'Solidity.Backend.InternalFlow.CallerView.represented', 'Solidity.Backend.InternalFlow.CallerView.different_array', 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.middle_pointers', 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.middle_endpoint', 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.old_inputs', 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.middle_snapshot']
PINS = {'Solidity.Backend.InternalFlow.CallerView.by_id': [], 'Solidity.Backend.InternalFlow.CallerView.reference': ['propext'], 'Solidity.Backend.InternalFlow.CallerView.represented': ['Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.CallerView.different_array': ['Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.middle_pointers': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.middle_endpoint': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.old_inputs': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.middle_snapshot': ['Classical.choice', 'Quot.sound', 'propext']}
PATTERN = r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
def check(text):
    if re.search(r"(?:^|\n).*?(?:error:|error\(|sorryAx)", text):
        raise ValueError("diagnostic or untrusted axiom in builtin audit")
    reports = [(n, sorted(x.strip() for x in a.split(',') if x.strip()))
               for n, a in re.findall(PATTERN, text)]
    expected = [(n, PINS[n]) for n in NAMES]
    if reports != expected:
        raise ValueError("missing, reordered, duplicate or changed caller-view axiom report")
    return len(reports)
if __name__ == '__main__':
    try:
        count = check(Path(sys.argv[1]).read_text())
    except (ValueError, OSError, IndexError) as error:
        print(str(error), file=sys.stderr)
        sys.exit(1)
    print(json.dumps({'status': 'pass', 'actual_builtin_reports': count}))
