#!/usr/bin/env python3
"""Guard actual unmodified builtin reports for the captured caller-tail consumer.
Run on the separately checked import query; it does not replace kernel checking
or the unchanged original542-report fixture inventory.
"""
import json
from pathlib import Path
import re
import sys
NAMES = ['Solidity.Backend.InternalFlow.CallerTail.program_environment', 'Solidity.Backend.InternalFlow.CallerTail.environment', 'Solidity.Backend.InternalFlow.CallerTail.alias', 'Solidity.Backend.InternalFlow.CallerTail.selected_target', 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.tail_within', 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.tail_unwritten', 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.complete_caller_frame', 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.whole_body_guard_stays_false', 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.wrong_destination', 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.reference_ids_wk', 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.full_frame_changes', 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.protected_alias_id', 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.post_step', 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.protected_final_frame']
PINS = {'Solidity.Backend.InternalFlow.CallerTail.program_environment': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.CallerTail.environment': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.CallerTail.alias': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.CallerTail.selected_target': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.tail_within': ['propext'], 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.tail_unwritten': ['Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.complete_caller_frame': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.whole_body_guard_stays_false': ['propext'], 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.wrong_destination': ['Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.reference_ids_wk': ['propext'], 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.full_frame_changes': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.protected_alias_id': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.post_step': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.protected_final_frame': ['Classical.choice', 'Quot.sound', 'propext']}
PATTERN = r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
def check(text):
    if re.search(r"(?:^|\n).*?(?:error:|error\(|sorryAx)", text):
        raise ValueError("diagnostic or untrusted axiom in builtin audit")
    reports = [(n, sorted(x.strip() for x in a.split(',') if x.strip()))
               for n, a in re.findall(PATTERN, text)]
    expected = [(n, PINS[n]) for n in NAMES]
    if reports != expected:
        raise ValueError("missing, reordered, duplicate or changed caller-tail axiom report")
    return len(reports)
if __name__ == '__main__':
    try:
        count = check(Path(sys.argv[1]).read_text())
    except (ValueError, OSError, IndexError) as error:
        print(str(error), file=sys.stderr)
        sys.exit(1)
    print(json.dumps({'status': 'pass', 'actual_builtin_reports': count}))
